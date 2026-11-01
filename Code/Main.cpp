// ============================================================================
//  ESP32 Hub  -  LVGL touchscreen controller for Spotify + Govee + BT speakers
//
//  * Spotify : OAuth 2.0 Authorization Code + PKCE (browser page, QR on screen)
//  * Govee   : Govee Developer API (uses an API KEY, not OAuth - see README text)
//  * Bluetooth: ESP32 acts as an A2DP *source* and streams to a BT speaker
//
//  "Pop-up" login pages: an ESP32 cannot embed a web view, so the device shows a
//  modal with a QR code. You scan it with your phone, which opens a page served
//  by the ESP32 itself (Govee) or redirects to Spotify's login (Spotify).
// ============================================================================
#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <HTTPClient.h>
#include <WiFiClientSecure.h>
#include <Preferences.h>
#include <ArduinoJson.h>
#include <SPI.h>
#include <TFT_eSPI.h>
#include <XPT2046_Touchscreen.h>
#include <lvgl.h>
#include <BluetoothA2DPSource.h>
#include <mbedtls/sha256.h>
#include <mbedtls/base64.h>
#include <vector>

// ------------------------------- USER CONFIG --------------------------------
#define WIFI_SSID            "YOUR_WIFI"
#define WIFI_PASS            "YOUR_PASSWORD"

// Create an app at https://developer.spotify.com/dashboard and paste its Client ID.
#define SPOTIFY_CLIENT_ID    "YOUR_SPOTIFY_CLIENT_ID"
// Must EXACTLY match a Redirect URI registered in the dashboard.
// Spotify no longer allows plain-http LAN addresses, so the default is the loopback
// address: after login the phone's browser shows "can't connect", you copy that
// address and paste it at http://<esp-ip>/paste (the on-screen hint says so).
// Better: host a tiny https relay page and register that instead (see bottom of file).
#define SPOTIFY_REDIRECT_URI "http://127.0.0.1:8888/callback"
#define SPOTIFY_SCOPES       "user-read-playback-state user-modify-playback-state user-read-currently-playing"
// -----------------------------------------------------------------------------

static const uint16_t SCR_W = 320, SCR_H = 240;

// ------------------------------- Display / touch ----------------------------
TFT_eSPI tft;
SPIClass touchSPI(VSPI);
XPT2046_Touchscreen ts(33, 36);
static lv_disp_draw_buf_t drawBuf;
static lv_color_t buf1[SCR_W * 24];

static void flushCb(lv_disp_drv_t* d, const lv_area_t* a, lv_color_t* c) {
  uint32_t w = a->x2 - a->x1 + 1, h = a->y2 - a->y1 + 1;
  tft.startWrite();
  tft.setAddrWindow(a->x1, a->y1, w, h);
  tft.pushColors((uint16_t*)&c->full, w * h, true);
  tft.endWrite();
  lv_disp_flush_ready(d);
}
static void touchCb(lv_indev_drv_t*, lv_indev_data_t* data) {
  if (ts.tirqTouched() && ts.touched()) {
    TS_Point p = ts.getPoint();
    data->point.x = constrain(map(p.x, 200, 3700, 0, SCR_W), 0, SCR_W - 1);
    data->point.y = constrain(map(p.y, 240, 3800, 0, SCR_H), 0, SCR_H - 1);
    data->state = LV_INDEV_STATE_PR;
  } else {
    data->state = LV_INDEV_STATE_REL;
  }
}

// ------------------------------- Shared state -------------------------------
SemaphoreHandle_t mtx;
struct Lock {
  Lock()  { xSemaphoreTakeRecursive(mtx, portMAX_DELAY); }
  ~Lock() { xSemaphoreGiveRecursive(mtx); }
};
Preferences prefs;
static void savePref(const char* k, const String& v) { Lock l; prefs.putString(k, v); }

enum CmdType : uint8_t {
  C_GOVEE_REFRESH, C_GOVEE_POWER, C_GOVEE_BRIGHT, C_GOVEE_COLOR, C_GOVEE_TEMP,
  C_SP_EXCHANGE, C_SP_POLL, C_SP_PLAYPAUSE, C_SP_NEXT, C_SP_PREV, C_SP_VOL
};
struct Cmd { CmdType t; int32_t a; int32_t idx; };
QueueHandle_t cmdQ;
static void post(CmdType t, int32_t a = 0, int32_t idx = 0) { Cmd c{t, a, idx}; xQueueSend(cmdQ, &c, 0); }

struct GoveeDev {
  String sku, id, name;
  bool power = false; int bright = 50;
  bool hasPower = false, hasBright = false, hasColor = false, hasTemp = false;
  int tMin = 2000, tMax = 9000;
};
static std::vector<GoveeDev> devs;
static int selDev = 0;
static String goveeKey;

static String spRefresh, spAccess, spVerifier, pendingCode;
static uint32_t spExpiresAt = 0;
struct SpState { String track = "Nothing playing", artist; bool playing = false; int volume = 50; } sp;

static std::vector<String> btFound;
static String btTarget;

static String toastMsg;
static volatile bool toastNew = false, devsDirty = false, spDirty = false, btDirty = false, authDone = false;

static void toast(const String& s) { Lock l; toastMsg = s; toastNew = true; Serial.println(s); }

// ------------------------------- Small helpers ------------------------------
static String urlenc(const String& s) {
  String o; char b[4];
  for (size_t i = 0; i < s.length(); i++) {
    char ch = s[i];
    if (isalnum((uint8_t)ch) || ch == '-' || ch == '_' || ch == '.' || ch == '~') o += ch;
    else { snprintf(b, sizeof b, "%%%02X", (uint8_t)ch); o += b; }
  }
  return o;
}
static String b64url(const uint8_t* d, size_t n) {
  unsigned char out[96]; size_t ol = 0;
  mbedtls_base64_encode(out, sizeof out - 1, &ol, d, n);
  out[ol] = 0;
  String s((char*)out);
  s.replace('+', '-'); s.replace('/', '_');
  while (s.endsWith("=")) s.remove(s.length() - 1);
  return s;
}

// ======================= BLUETOOTH A2DP SOURCE ==============================
BluetoothA2DPSource a2dp;
static bool btStarted = false, testTone = false;

#define RING_FRAMES 8192
static int16_t ringBuf[RING_FRAMES * 2];
static volatile uint32_t rHead = 0, rTail = 0;

// Feed 44.1 kHz / 16-bit / stereo PCM here (e.g. from a cspot Spotify Connect sink).
size_t audioPush(const int16_t* stereo, size_t frames) {
  size_t n = 0;
  while (n < frames) {
    uint32_t next = (rHead + 1) % RING_FRAMES;
    if (next == rTail) break;
    ringBuf[rHead * 2] = stereo[n * 2];
    ringBuf[rHead * 2 + 1] = stereo[n * 2 + 1];
    rHead = next; n++;
  }
  return n;
}
static int32_t a2dpData(Frame* f, int32_t count) {
  static float phase = 0;
  for (int32_t i = 0; i < count; i++) {
    if (testTone) {
      int16_t s = (int16_t)(sinf(phase) * 6000);
      phase += 2 * PI * 440.0f / 44100.0f; if (phase > 2 * PI) phase -= 2 * PI;
      f[i].channel1 = f[i].channel2 = s;
    } else if (rTail != rHead) {
      f[i].channel1 = ringBuf[rTail * 2];
      f[i].channel2 = ringBuf[rTail * 2 + 1];
      rTail = (rTail + 1) % RING_FRAMES;
    } else {
      f[i].channel1 = f[i].channel2 = 0;
    }
  }
  return count;
}
// Called from the BT task for every discovered device. Return true to connect to it.
static bool btSsidCb(const char* ssid, esp_bd_addr_t, int) {
  if (!ssid || !*ssid) return false;
  Lock l;
  bool known = false;
  for (auto& n : btFound) if (n == ssid) known = true;
  if (!known) { btFound.push_back(ssid); btDirty = true; }
  return btTarget.length() && btTarget == ssid;
}
static void btStart() {
  if (btStarted) return;
  a2dp.set_ssid_callback(btSsidCb);
  a2dp.set_data_callback_in_frames(a2dpData);
  a2dp.set_auto_reconnect(false);
  a2dp.set_volume(64);
  a2dp.start("__scan__");   // placeholder name; the callback decides what to connect to
  btStarted = true;
}
static void btSelect(const String& name) {
  { Lock l; btTarget = name; }
  savePref("bt", name);
  if (btStarted) { a2dp.end(); btStarted = false; delay(300); }
  btStart();
  toast("Connecting to " + name + "...");
}

// ============================ SPOTIFY (OAuth PKCE) ===========================
static void makePkce() {
  const char cs[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~";
  char v[65];
  for (int i = 0; i < 64; i++) v[i] = cs[esp_random() % (sizeof(cs) - 1)];
  v[64] = 0;
  spVerifier = v;
}
static String spotifyAuthUrl() {
  uint8_t h[32];
  mbedtls_sha256((const uint8_t*)spVerifier.c_str(), spVerifier.length(), h, 0);
  return String("https://accounts.spotify.com/authorize?response_type=code&client_id=") + SPOTIFY_CLIENT_ID +
         "&scope=" + urlenc(SPOTIFY_SCOPES) + "&redirect_uri=" + urlenc(SPOTIFY_REDIRECT_URI) +
         "&code_challenge_method=S256&code_challenge=" + b64url(h, 32) +
         "&state=" + WiFi.localIP().toString();   // lets an https relay page forward to the ESP
}
static bool tokenRequest(const String& body) {
  WiFiClientSecure c; c.setInsecure();   // TODO: pin Spotify's root CA for production
  HTTPClient h;
  h.begin(c, "https://accounts.spotify.com/api/token");
  h.addHeader("Content-Type", "application/x-www-form-urlencoded");
  int code = h.POST(body);
  if (code != 200) { toast("Spotify token error " + String(code)); h.end(); return false; }
  JsonDocument d;
  deserializeJson(d, h.getString());
  h.end();
  spAccess = d["access_token"].as<String>();
  spExpiresAt = millis() + ((uint32_t)(d["expires_in"] | 3600) - 60) * 1000UL;
  if (d["refresh_token"].is<const char*>()) {
    spRefresh = d["refresh_token"].as<String>();
    savePref("spr", spRefresh);
  }
  return true;
}
static bool spEnsure() {
  if (spRefresh.isEmpty()) return false;
  if (spAccess.length() && (int32_t)(spExpiresAt - millis()) > 0) return true;
  return tokenRequest("grant_type=refresh_token&refresh_token=" + urlenc(spRefresh) +
                      "&client_id=" SPOTIFY_CLIENT_ID);
}
static int spCall(const char* method, const String& url, JsonDocument* out = nullptr, JsonDocument* filter = nullptr) {
  if (!spEnsure()) return -1;
  WiFiClientSecure c; c.setInsecure();
  HTTPClient h;
  h.useHTTP10(true);
  h.begin(c, url);
  h.addHeader("Authorization", "Bearer " + spAccess);
  int code;
  if (!strcmp(method, "GET")) code = h.GET();
  else { h.addHeader("Content-Type", "application/json"); code = h.sendRequest(method, "{}"); }
  if (code == 200 && out) {
    if (filter) deserializeJson(*out, h.getStream(), DeserializationOption::Filter(*filter));
    else deserializeJson(*out, h.getStream());
  }
  h.end();
  if (code == 404) toast("No active Spotify device. Start Spotify somewhere first.");
  else if (code == 403) toast("Spotify: Premium required for playback control");
  return code;
}
static void spPoll() {
  JsonDocument f, d;
  f["is_playing"] = true; f["item"]["name"] = true;
  f["item"]["artists"][0]["name"] = true; f["device"]["volume_percent"] = true;
  int code = spCall("GET", "https://api.spotify.com/v1/me/player", &d, &f);
  Lock l;
  if (code == 200) {
    sp.track = d["item"]["name"] | "Unknown";
    sp.artist = d["item"]["artists"][0]["name"] | "";
    sp.playing = d["is_playing"] | false;
    sp.volume = d["device"]["volume_percent"] | sp.volume;
    spDirty = true;
  } else if (code == 204) {
    sp.track = "Nothing playing"; sp.artist = ""; sp.playing = false; spDirty = true;
  }
}

// ============================== GOVEE (REST) =================================
static int goveeCall(const char* method, const char* path, const String& body,
                     JsonDocument* out, JsonDocument* filter = nullptr) {
  String key; { Lock l; key = goveeKey; }
  if (key.isEmpty()) return -1;
  WiFiClientSecure c; c.setInsecure();
  HTTPClient h;
  h.useHTTP10(true);
  h.begin(c, String("https://openapi.api.govee.com/router/api/v1") + path);
  h.addHeader("Govee-API-Key", key);
  h.addHeader("Content-Type", "application/json");
  int code = !strcmp(method, "GET") ? h.GET() : h.sendRequest(method, body);
  if (code == 200 && out) {
    if (filter) deserializeJson(*out, h.getStream(), DeserializationOption::Filter(*filter));
    else deserializeJson(*out, h.getStream());
  }
  h.end();
  return code;
}
static void goveeFetchState(GoveeDev& d) {
  JsonDocument b, doc;
  b["requestId"] = "state"; b["payload"]["sku"] = d.sku; b["payload"]["device"] = d.id;
  String body; serializeJson(b, body);
  if (goveeCall("POST", "/device/state", body, &doc) != 200) return;
  for (JsonObject c : doc["payload"]["capabilities"].as<JsonArray>()) {
    String in = c["instance"].as<String>();
    if (in == "powerSwitch") d.power = (c["state"]["value"] | 0) == 1;
    else if (in == "brightness") d.bright = c["state"]["value"] | 50;
  }
}
static void goveeRefresh() {
  JsonDocument f, doc;
  f["data"][0]["sku"] = true; f["data"][0]["device"] = true; f["data"][0]["deviceName"] = true;
  f["data"][0]["capabilities"][0]["instance"] = true;
  f["data"][0]["capabilities"][0]["parameters"]["range"] = true;
  int code = goveeCall("GET", "/user/devices", "", &doc, &f);
  if (code != 200) { toast("Govee error " + String(code) + " (check API key)"); return; }
  std::vector<GoveeDev> v;
  for (JsonObject o : doc["data"].as<JsonArray>()) {
    GoveeDev d;
    d.sku = o["sku"].as<String>(); d.id = o["device"].as<String>();
    d.name = o["deviceName"] | d.id.c_str();
    for (JsonObject c : o["capabilities"].as<JsonArray>()) {
      String in = c["instance"].as<String>();
      if (in == "powerSwitch") d.hasPower = true;
      else if (in == "brightness") d.hasBright = true;
      else if (in == "colorRgb") d.hasColor = true;
      else if (in == "colorTemperatureK") {
        d.hasTemp = true;
        d.tMin = c["parameters"]["range"]["min"] | 2000;
        d.tMax = c["parameters"]["range"]["max"] | 9000;
      }
    }
    v.push_back(d);
  }
  for (auto& d : v) goveeFetchState(d);
  { Lock l; devs = v; if (selDev >= (int)devs.size()) selDev = 0; devsDirty = true; }
  toast(String(v.size()) + " Govee device(s) found");
}
static void goveeControl(const GoveeDev& d, const char* type, const char* inst, long value) {
  JsonDocument j, doc;
  j["requestId"] = String(millis());
  j["payload"]["sku"] = d.sku; j["payload"]["device"] = d.id;
  j["payload"]["capability"]["type"] = type;
  j["payload"]["capability"]["instance"] = inst;
  j["payload"]["capability"]["value"] = value;
  String body; serializeJson(j, body);
  int code = goveeCall("POST", "/device/control", body, &doc);
  if (code != 200) toast("Govee control failed: " + String(code) + " (limit ~10 req/min/device)");
}

// ================================ Worker task ================================
static bool getDev(int idx, GoveeDev& out) {
  Lock l;
  if (idx < 0 || idx >= (int)devs.size()) return false;
  out = devs[idx]; return true;
}
static void handle(const Cmd& c) {
  GoveeDev d;
  switch (c.t) {
    case C_GOVEE_REFRESH: goveeRefresh(); break;
    case C_GOVEE_POWER:  if (getDev(c.idx, d)) goveeControl(d, "devices.capabilities.on_off", "powerSwitch", c.a); break;
    case C_GOVEE_BRIGHT: if (getDev(c.idx, d)) goveeControl(d, "devices.capabilities.range", "brightness", c.a); break;
    case C_GOVEE_COLOR:  if (getDev(c.idx, d)) goveeControl(d, "devices.capabilities.color_setting", "colorRgb", c.a); break;
    case C_GOVEE_TEMP:   if (getDev(c.idx, d)) goveeControl(d, "devices.capabilities.color_setting", "colorTemperatureK", c.a); break;
    case C_SP_EXCHANGE: {
      String code; { Lock l; code = pendingCode; }
      bool ok = tokenRequest("grant_type=authorization_code&code=" + urlenc(code) +
                             "&redirect_uri=" + urlenc(SPOTIFY_REDIRECT_URI) +
                             "&client_id=" SPOTIFY_CLIENT_ID "&code_verifier=" + spVerifier);
      if (ok) { toast("Spotify connected"); authDone = true; spPoll(); }
      break;
    }
    case C_SP_POLL: spPoll(); break;
    case C_SP_PLAYPAUSE: {
      bool playing; { Lock l; playing = sp.playing; }
      spCall("PUT", String("https://api.spotify.com/v1/me/player/") + (playing ? "pause" : "play"));
      vTaskDelay(pdMS_TO_TICKS(400)); spPoll(); break;
    }
    case C_SP_NEXT: spCall("POST", "https://api.spotify.com/v1/me/player/next"); vTaskDelay(pdMS_TO_TICKS(600)); spPoll(); break;
    case C_SP_PREV: spCall("POST", "https://api.spotify.com/v1/me/player/previous"); vTaskDelay(pdMS_TO_TICKS(600)); spPoll(); break;
    case C_SP_VOL: spCall("PUT", "https://api.spotify.com/v1/me/player/volume?volume_percent=" + String(c.a)); break;
  }
}
static void netTask(void*) {
  Cmd c; uint32_t lastPoll = 0;
  for (;;) {
    if (xQueueReceive(cmdQ, &c, pdMS_TO_TICKS(500)) == pdTRUE) handle(c);
    if (WiFi.status() == WL_CONNECTED && spRefresh.length() && millis() - lastPoll > 5000) {
      lastPoll = millis(); spPoll();
    }
  }
}

// ================================ Web server =================================
WebServer web(80);
static bool webStarted = false;
static String page(const String& body) {
  return "<!doctype html><meta name=viewport content='width=device-width,initial-scale=1'>"
         "<style>body{font-family:sans-serif;max-width:480px;margin:2em auto;padding:0 1em}"
         "input,button,textarea{width:100%;padding:.7em;margin:.4em 0;font-size:1em;box-sizing:border-box}</style>" + body;
}
static void hRoot() {
  web.send(200, "text/html", page("<h2>ESP32 Hub</h2><p><a href='/govee'>Link Govee</a></p>"
                                  "<p><a href='/spotify'>Link Spotify</a></p><p><a href='/paste'>Paste Spotify redirect URL</a></p>"));
}
static void hGovee() {
  if (web.method() == HTTP_POST) {
    String k = web.arg("key"); k.trim();
    if (k.length() < 10) { web.send(400, "text/html", page("<p>That key looks too short.</p>")); return; }
    { Lock l; goveeKey = k; }
    savePref("gkey", k);
    post(C_GOVEE_REFRESH);
    authDone = true;
    web.send(200, "text/html", page("<h3>Govee linked</h3><p>You can close this page.</p>"));
    return;
  }
  web.send(200, "text/html", page(
    "<h3>Link Govee Home</h3><p>In the Govee Home app: Profile &rarr; Settings &rarr; <b>Apply for API Key</b>. "
    "Govee emails you the key. Paste it here.</p><form method=post><input name=key placeholder='API key' autocomplete=off>"
    "<button>Save</button></form>"));
}
static void hSpotify() {
  if (String(SPOTIFY_CLIENT_ID).startsWith("YOUR_")) { web.send(500, "text/plain", "Set SPOTIFY_CLIENT_ID in firmware."); return; }
  makePkce();
  web.sendHeader("Location", spotifyAuthUrl());
  web.send(302, "text/plain", "");
}
static void gotCode(const String& code) { { Lock l; pendingCode = code; } post(C_SP_EXCHANGE); }
static void hCallback() {   // used when an https relay forwards to http://<esp-ip>/callback?code=...
  if (web.hasArg("code")) { gotCode(web.arg("code")); web.send(200, "text/html", page("<h3>Spotify linked</h3><p>You can close this page.</p>")); }
  else web.send(400, "text/html", page("<p>Authorization failed: " + web.arg("error") + "</p>"));
}
static void hPaste() {
  if (web.method() == HTTP_POST) {
    String u = web.arg("url"); int i = u.indexOf("code=");
    if (i < 0) { web.send(400, "text/html", page("<p>No <code>code=</code> found in that text.</p>")); return; }
    String code = u.substring(i + 5); int j = code.indexOf('&'); if (j >= 0) code = code.substring(0, j);
    code.trim(); gotCode(code);
    web.send(200, "text/html", page("<h3>Spotify linked</h3><p>You can close this page.</p>")); return;
  }
  web.send(200, "text/html", page("<h3>Paste Spotify redirect address</h3><p>After approving, your browser tries to open "
    "127.0.0.1 and fails. Copy the full address from the address bar and paste it here.</p>"
    "<form method=post><textarea name=url rows=5></textarea><button>Finish</button></form>"));
}

// =================================== UI ======================================
static lv_obj_t *lblTrack, *lblArtist, *lblPP, *sldSpVol;
static lv_obj_t *ddDev, *swPower, *sldBri, *sldTemp, *cw;
static lv_obj_t *listBt, *lblBt, *lblNet, *lblGv, *lblSp, *toastLbl, *modal;

static void closeModal() { if (modal) { lv_obj_del(modal); modal = nullptr; } }
static void showAuthModal(const char* title, const String& url, const String& hint) {
  closeModal();
  modal = lv_obj_create(lv_layer_top());           // full-screen backdrop blocks touches underneath
  lv_obj_set_size(modal, SCR_W, SCR_H);
  lv_obj_set_style_bg_color(modal, lv_color_black(), 0);
  lv_obj_set_style_bg_opa(modal, LV_OPA_70, 0);
  lv_obj_set_style_border_width(modal, 0, 0);
  lv_obj_set_style_radius(modal, 0, 0);
  lv_obj_clear_flag(modal, LV_OBJ_FLAG_SCROLLABLE);
  lv_obj_t* card = lv_obj_create(modal);
  lv_obj_set_size(card, 308, 228); lv_obj_center(card);
  lv_obj_clear_flag(card, LV_OBJ_FLAG_SCROLLABLE);
  lv_obj_t* t = lv_label_create(card); lv_label_set_text(t, title);
  lv_obj_set_style_text_font(t, &lv_font_montserrat_20, 0); lv_obj_align(t, LV_ALIGN_TOP_LEFT, 0, 0);
  lv_obj_t* qr = lv_qrcode_create(card, 128, lv_color_black(), lv_color_white());
  lv_qrcode_update(qr, url.c_str(), url.length());
  lv_obj_set_style_border_color(qr, lv_color_white(), 0); lv_obj_set_style_border_width(qr, 5, 0);
  lv_obj_align(qr, LV_ALIGN_TOP_LEFT, 0, 34);
  lv_obj_t* h = lv_label_create(card);
  lv_label_set_long_mode(h, LV_LABEL_LONG_WRAP); lv_obj_set_width(h, 150);
  lv_label_set_text(h, hint.c_str()); lv_obj_align(h, LV_ALIGN_TOP_LEFT, 140, 34);
  lv_obj_t* u = lv_label_create(card); lv_label_set_text(u, url.length() < 40 ? url.c_str() : "");
  lv_obj_align(u, LV_ALIGN_BOTTOM_LEFT, 0, 0);
  lv_obj_t* b = lv_btn_create(card); lv_obj_align(b, LV_ALIGN_BOTTOM_RIGHT, 0, 0);
  lv_obj_t* bl = lv_label_create(b); lv_label_set_text(bl, "Close");
  lv_obj_add_event_cb(b, [](lv_event_t*) { closeModal(); }, LV_EVENT_CLICKED, nullptr);
}
static void syncGoveeControls() {   // UI thread only
  Lock l;
  if (devs.empty() || selDev >= (int)devs.size()) return;
  GoveeDev& d = devs[selDev];
  if (d.power) lv_obj_add_state(swPower, LV_STATE_CHECKED); else lv_obj_clear_state(swPower, LV_STATE_CHECKED);
  lv_slider_set_value(sldBri, d.bright, LV_ANIM_OFF);
  lv_slider_set_range(sldTemp, d.tMin, d.tMax);
  (d.hasBright ? lv_obj_clear_state : lv_obj_add_state)(sldBri, LV_STATE_DISABLED);
  (d.hasTemp ? lv_obj_clear_state : lv_obj_add_state)(sldTemp, LV_STATE_DISABLED);
  (d.hasColor ? lv_obj_clear_state : lv_obj_add_state)(cw, LV_STATE_DISABLED);
  (d.hasPower ? lv_obj_clear_state : lv_obj_add_state)(swPower, LV_STATE_DISABLED);
}
static void uiSync(lv_timer_t*) {
  bool t, dd, s, b, a; String tm;
  { Lock l; t = toastNew; tm = toastMsg; toastNew = false; dd = devsDirty; devsDirty = false;
    s = spDirty; spDirty = false; b = btDirty; btDirty = false; a = authDone; authDone = false; }
  if (t) {
    lv_label_set_text(toastLbl, tm.c_str());
    lv_obj_fade_in(toastLbl, 150, 0); lv_obj_fade_out(toastLbl, 400, 3500);
  }
  if (a) closeModal();
  if (dd) {
    String opts;
    { Lock l; for (size_t i = 0; i < devs.size(); i++) { if (i) opts += "\n"; opts += devs[i].name; } }
    lv_dropdown_set_options(ddDev, opts.length() ? opts.c_str() : "No devices");
    lv_dropdown_set_selected(ddDev, selDev);
    syncGoveeControls();
  }
  if (s) {
    Lock l;
    lv_label_set_text(lblTrack, sp.track.c_str()); lv_label_set_text(lblArtist, sp.artist.c_str());
    lv_label_set_text(lblPP, sp.playing ? LV_SYMBOL_PAUSE : LV_SYMBOL_PLAY);
    lv_slider_set_value(sldSpVol, sp.volume, LV_ANIM_OFF);
  }
  if (b) {
    lv_obj_clean(listBt);
    Lock l;
    for (auto& n : btFound) {
      lv_obj_t* btn = lv_list_add_btn(listBt, LV_SYMBOL_BLUETOOTH, n.c_str());
      lv_obj_add_event_cb(btn, [](lv_event_t* e) {
        btSelect(String(lv_list_get_btn_text(listBt, lv_event_get_target(e))));
      }, LV_EVENT_CLICKED, nullptr);
    }
  }
  lv_label_set_text_fmt(lblBt, "BT: %s", a2dp.is_connected() ? "connected" : (btStarted ? "scanning/connecting" : "off"));
  lv_label_set_text_fmt(lblNet, "WiFi: %s", WiFi.status() == WL_CONNECTED ? WiFi.localIP().toString().c_str() : "connecting...");
  { Lock l;
    lv_label_set_text_fmt(lblGv, "Govee: %s", goveeKey.length() ? "linked" : "not linked");
    lv_label_set_text_fmt(lblSp, "Spotify: %s", spRefresh.length() ? "linked" : "not linked"); }
}

static lv_obj_t* mkBtn(lv_obj_t* parent, const char* txt, lv_event_cb_t cb, void* ud, int w = 60) {
  lv_obj_t* b = lv_btn_create(parent); lv_obj_set_size(b, w, 42);
  lv_obj_t* l = lv_label_create(b); lv_label_set_text(l, txt); lv_obj_center(l);
  lv_obj_add_event_cb(b, cb, LV_EVENT_CLICKED, ud);
  return b;
}
static void buildMusic(lv_obj_t* tab) {
  lblTrack = lv_label_create(tab); lv_obj_set_width(lblTrack, 290);
  lv_label_set_long_mode(lblTrack, LV_LABEL_LONG_SCROLL_CIRCULAR);
  lv_obj_set_style_text_font(lblTrack, &lv_font_montserrat_20, 0); lv_label_set_text(lblTrack, "Nothing playing");
  lblArtist = lv_label_create(tab); lv_obj_set_width(lblArtist, 290);
  lv_label_set_long_mode(lblArtist, LV_LABEL_LONG_DOT); lv_label_set_text(lblArtist, "");
  lv_obj_align(lblArtist, LV_ALIGN_TOP_LEFT, 0, 30);
  auto cb = [](lv_event_t* e) {
    intptr_t k = (intptr_t)lv_event_get_user_data(e);
    post(k == 0 ? C_SP_PREV : k == 1 ? C_SP_PLAYPAUSE : C_SP_NEXT);
  };
  lv_obj_t* b0 = mkBtn(tab, LV_SYMBOL_PREV, cb, (void*)0);  lv_obj_align(b0, LV_ALIGN_TOP_LEFT, 20, 60);
  lv_obj_t* b1 = mkBtn(tab, LV_SYMBOL_PLAY, cb, (void*)1);  lv_obj_align(b1, LV_ALIGN_TOP_MID, 0, 60);
  lblPP = lv_obj_get_child(b1, 0);
  lv_obj_t* b2 = mkBtn(tab, LV_SYMBOL_NEXT, cb, (void*)2);  lv_obj_align(b2, LV_ALIGN_TOP_RIGHT, -20, 60);
  lv_obj_t* vl = lv_label_create(tab); lv_label_set_text(vl, LV_SYMBOL_VOLUME_MAX); lv_obj_align(vl, LV_ALIGN_TOP_LEFT, 0, 120);
  sldSpVol = lv_slider_create(tab); lv_obj_set_width(sldSpVol, 240); lv_obj_align(sldSpVol, LV_ALIGN_TOP_LEFT, 36, 124);
  lv_obj_add_event_cb(sldSpVol, [](lv_event_t* e) { post(C_SP_VOL, lv_slider_get_value(lv_event_get_target(e))); },
                      LV_EVENT_RELEASED, nullptr);
}
static void buildLights(lv_obj_t* tab) {
  ddDev = lv_dropdown_create(tab); lv_obj_set_width(ddDev, 290); lv_dropdown_set_options(ddDev, "No devices");
  lv_obj_add_event_cb(ddDev, [](lv_event_t* e) {
    selDev = lv_dropdown_get_selected(lv_event_get_target(e)); syncGoveeControls();
  }, LV_EVENT_VALUE_CHANGED, nullptr);
  swPower = lv_switch_create(tab); lv_obj_align(swPower, LV_ALIGN_TOP_LEFT, 0, 48);
  lv_obj_add_event_cb(swPower, [](lv_event_t* e) {
    post(C_GOVEE_POWER, lv_obj_has_state(lv_event_get_target(e), LV_STATE_CHECKED) ? 1 : 0, selDev);
  }, LV_EVENT_VALUE_CHANGED, nullptr);
  sldBri = lv_slider_create(tab); lv_slider_set_range(sldBri, 1, 100);
  lv_obj_set_width(sldBri, 200); lv_obj_align(sldBri, LV_ALIGN_TOP_LEFT, 80, 56);
  lv_obj_add_event_cb(sldBri, [](lv_event_t* e) { post(C_GOVEE_BRIGHT, lv_slider_get_value(lv_event_get_target(e)), selDev); },
                      LV_EVENT_RELEASED, nullptr);
  lv_obj_t* l1 = lv_label_create(tab); lv_label_set_text(l1, "White temp (K)"); lv_obj_align(l1, LV_ALIGN_TOP_LEFT, 0, 86);
  sldTemp = lv_slider_create(tab); lv_slider_set_range(sldTemp, 2000, 9000);
  lv_obj_set_width(sldTemp, 270); lv_obj_align(sldTemp, LV_ALIGN_TOP_LEFT, 8, 112);
  lv_obj_add_event_cb(sldTemp, [](lv_event_t* e) { post(C_GOVEE_TEMP, lv_slider_get_value(lv_event_get_target(e)), selDev); },
                      LV_EVENT_RELEASED, nullptr);
  cw = lv_colorwheel_create(tab, true); lv_obj_set_size(cw, 130, 130); lv_obj_align(cw, LV_ALIGN_TOP_MID, 0, 130);
  lv_obj_add_event_cb(cw, [](lv_event_t* e) {
    uint32_t rgb = lv_color_to32(lv_colorwheel_get_rgb(lv_event_get_target(e))) & 0xFFFFFF;
    post(C_GOVEE_COLOR, rgb, selDev);
  }, LV_EVENT_RELEASED, nullptr);
}
static void buildBt(lv_obj_t* tab) {
  lblBt = lv_label_create(tab); lv_label_set_text(lblBt, "BT: off");
  lv_obj_t* scan = mkBtn(tab, "Scan", [](lv_event_t*) {
    { Lock l; btFound.clear(); btTarget = ""; }
    if (btStarted) { a2dp.end(); btStarted = false; delay(300); }
    btStart(); toast("Scanning... turn your speaker's pairing mode on");
  }, nullptr, 70);
  lv_obj_align(scan, LV_ALIGN_TOP_RIGHT, 0, -6);
  listBt = lv_list_create(tab); lv_obj_set_size(listBt, 290, 90); lv_obj_align(listBt, LV_ALIGN_TOP_LEFT, 0, 40);
  lv_obj_t* tone = mkBtn(tab, "Test tone", [](lv_event_t* e) {
    testTone = !testTone;
  }, nullptr, 110);
  lv_obj_align(tone, LV_ALIGN_TOP_LEFT, 0, 136);
  lv_obj_t* sl = lv_slider_create(tab); lv_slider_set_range(sl, 0, 127); lv_slider_set_value(sl, 64, LV_ANIM_OFF);
  lv_obj_set_width(sl, 150); lv_obj_align(sl, LV_ALIGN_TOP_LEFT, 130, 152);
  lv_obj_add_event_cb(sl, [](lv_event_t* e) { a2dp.set_volume(lv_slider_get_value(lv_event_get_target(e))); },
                      LV_EVENT_VALUE_CHANGED, nullptr);
}
static void buildSetup(lv_obj_t* tab) {
  lblNet = lv_label_create(tab); lblGv = lv_label_create(tab); lblSp = lv_label_create(tab);
  lv_obj_align(lblNet, LV_ALIGN_TOP_LEFT, 0, 0);
  lv_obj_align(lblGv, LV_ALIGN_TOP_LEFT, 0, 22);
  lv_obj_align(lblSp, LV_ALIGN_TOP_LEFT, 0, 44);
  lv_obj_t* g = mkBtn(tab, "Link Govee", [](lv_event_t*) {
    if (WiFi.status() != WL_CONNECTED) { toast("Connect WiFi first"); return; }
    showAuthModal("Link Govee", "http://" + WiFi.localIP().toString() + "/govee",
                  "Scan with your phone, then paste your Govee API key (Govee Home app > Profile > Settings > Apply for API Key).");
  }, nullptr, 140);
  lv_obj_align(g, LV_ALIGN_TOP_LEFT, 0, 72);
  lv_obj_t* s = mkBtn(tab, "Link Spotify", [](lv_event_t*) {
    if (WiFi.status() != WL_CONNECTED) { toast("Connect WiFi first"); return; }
    String ip = WiFi.localIP().toString();
    showAuthModal("Link Spotify", "http://" + ip + "/spotify",
                  "Scan, log in to Spotify and approve. If the final page fails to load, copy its address and paste it at http://" + ip + "/paste");
  }, nullptr, 140);
  lv_obj_align(s, LV_ALIGN_TOP_RIGHT, 0, 72);
  lv_obj_t* f = mkBtn(tab, "Forget accounts", [](lv_event_t*) {
    { Lock l; goveeKey = ""; spRefresh = ""; spAccess = ""; devs.clear(); devsDirty = true; }
    savePref("gkey", ""); savePref("spr", ""); toast("Accounts removed");
  }, nullptr, 290);
  lv_obj_align(f, LV_ALIGN_TOP_LEFT, 0, 122);
}
static void buildUi() {
  lv_theme_default_init(lv_disp_get_default(), lv_palette_main(LV_PALETTE_GREEN), lv_palette_main(LV_PALETTE_BLUE), true, &lv_font_montserrat_14);
  lv_obj_t* tv = lv_tabview_create(lv_scr_act(), LV_DIR_BOTTOM, 38);
  buildMusic(lv_tabview_add_tab(tv, LV_SYMBOL_AUDIO " Music"));
  buildLights(lv_tabview_add_tab(tv, LV_SYMBOL_IMAGE " Lights"));
  buildBt(lv_tabview_add_tab(tv, LV_SYMBOL_BLUETOOTH " Speaker"));
  buildSetup(lv_tabview_add_tab(tv, LV_SYMBOL_SETTINGS " Setup"));
  lv_obj_clear_flag(lv_tabview_get_content(tv), LV_OBJ_FLAG_SCROLL_ELASTIC);
  toastLbl = lv_label_create(lv_layer_top());
  lv_obj_set_style_bg_color(toastLbl, lv_color_black(), 0); lv_obj_set_style_bg_opa(toastLbl, LV_OPA_80, 0);
  lv_obj_set_style_pad_all(toastLbl, 5, 0); lv_label_set_long_mode(toastLbl, LV_LABEL_LONG_WRAP);
  lv_obj_set_width(toastLbl, 300); lv_obj_align(toastLbl, LV_ALIGN_BOTTOM_MID, 0, -44);
  lv_obj_set_style_opa(toastLbl, LV_OPA_TRANSP, 0);
  lv_timer_create(uiSync, 250, nullptr);
}

// ================================ Arduino ====================================
static uint32_t lastTick = 0;
void setup() {
  Serial.begin(115200);
  mtx = xSemaphoreCreateRecursiveMutex();
  cmdQ = xQueueCreate(16, sizeof(Cmd));
  prefs.begin("hub", false);
  goveeKey = prefs.getString("gkey", ""); spRefresh = prefs.getString("spr", ""); btTarget = prefs.getString("bt", "");

  tft.init(); tft.setRotation(1); tft.fillScreen(TFT_BLACK);
  pinMode(21, OUTPUT); digitalWrite(21, HIGH);
  touchSPI.begin(25, 39, 32, 33); ts.begin(touchSPI); ts.setRotation(1);

  lv_init();
  lv_disp_draw_buf_init(&drawBuf, buf1, nullptr, SCR_W * 24);
  static lv_disp_drv_t dd; lv_disp_drv_init(&dd);
  dd.hor_res = SCR_W; dd.ver_res = SCR_H; dd.flush_cb = flushCb; dd.draw_buf = &drawBuf; lv_disp_drv_register(&dd);
  static lv_indev_drv_t id; lv_indev_drv_init(&id); id.type = LV_INDEV_TYPE_POINTER; id.read_cb = touchCb; lv_indev_drv_register(&id);
  buildUi();

  WiFi.mode(WIFI_STA); WiFi.begin(WIFI_SSID, WIFI_PASS);
  web.on("/", hRoot); web.on("/govee", HTTP_ANY, hGovee); web.on("/spotify", hSpotify);
  web.on("/callback", hCallback); web.on("/paste", HTTP_ANY, hPaste);

  xTaskCreatePinnedToCore(netTask, "net", 12288, nullptr, 1, nullptr, 0);
  if (btTarget.length()) btStart();   // auto-reconnect to the last speaker
}
void loop() {
  uint32_t now = millis(); lv_tick_inc(now - lastTick); lastTick = now;
  lv_timer_handler();
  if (WiFi.status() == WL_CONNECTED) {
    if (!webStarted) {
      web.begin(); webStarted = true;
      if (goveeKey.length()) post(C_GOVEE_REFRESH);
    }
    web.handleClient();
  }
  delay(5);
}

/* ---------------------------------------------------------------------------
   OPTIONAL https relay for Spotify (removes the copy/paste step)
   Host this at e.g. https://YOURNAME.github.io/spotify-relay.html, register that
   exact URL as the Redirect URI, and set SPOTIFY_REDIRECT_URI to it:

   <script>
     const p = new URLSearchParams(location.search);
     // 'state' carries the ESP32's LAN IP (set in spotifyAuthUrl)
     location = "http://" + p.get("state") + "/callback?code=" + encodeURIComponent(p.get("code"));
   </script>
   --------------------------------------------------------------------------- */