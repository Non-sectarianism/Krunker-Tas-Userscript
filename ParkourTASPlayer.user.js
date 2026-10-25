// ==UserScript==
// @name         Krunker Parkour TAS Player
// @namespace    local.krunker.parkour.tas
// @version      1.0.3
// @description  Replays Parkour TAS Recorder JSON routes through procInputs with drift checks.
// @match        https://krunker.io/*
// @match        https://*.browserfps.com/*
// @run-at       document-start
// @grant        unsafeWindow
// ==/UserScript==

(function () {
  'use strict';

  const win = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
  const START_TOLERANCE = 0.5;
  const ALIGN_START_TOLERANCE = 10;
  const ALIGN_DONE_XZ = 0.45;
  const ALIGN_DONE_Y = 1.25;
  const ALIGN_SETTLE_HVEL = 0.018;
  const ALIGN_TIMEOUT_MS = 9000;
  const WARN_DRIFT = 8;
  const CFG_KEY = 'parkourTasPlayerCfg.v3';
  const TAS_DT_CAP_MS = 20;
  const TAS_SNAP_SUBFRAMES = 33;
  const TAS_SNAP_DT_EACH = 1.1;
  const TAS_R_SLOW_SUBFRAMES = 1;
  const TAS_R_SLOW_DT_EACH = 0.0033;
  const MOVE_DIRS = [];
  for (let i = 0; i < 8; i++) MOVE_DIRS.push(-Math.PI + (i + 1) * Math.PI / 4);

  function loadCfg() {
    try {
      return Object.assign({
        hardDrift: 100,
        recordedDt: true,
        timeSync: false,
      }, JSON.parse(localStorage.getItem(CFG_KEY) || '{}'));
    } catch {
      return { hardDrift: 100, recordedDt: true, timeSync: false };
    }
  }

  function saveCfg() {
    try { localStorage.setItem(CFG_KEY, JSON.stringify(cfg)); } catch {}
  }

  let cfg = loadCfg();

  let Game = null;
  let localPlayer = null;
  const hookedPlayers = new WeakSet();

  let route = null;
  let frames = [];
  let playing = false;
  let aligning = false;
  let alignStarted = 0;
  let alignFrame = 0;
  let alignBest = Infinity;
  let playIndex = 0;
  let playElapsed = 0;
  let routeStartT = 0;
  let maxDrift = 0;
  let lastStatus = 'load route';

  function finite(v, fallback = 0) {
    return (typeof v === 'number' && isFinite(v)) ? v : fallback;
  }

  function round(v, d = 4) {
    if (typeof v !== 'number' || !isFinite(v)) return 0;
    const m = Math.pow(10, d);
    return Math.round(v * m) / m;
  }

  function tasDtCapMs() {
    return Math.max(0.1, finite(win.__parkourTasSnap?.dtCapMs, TAS_DT_CAP_MS));
  }

  function tasSnapSubframes() {
    return Math.max(1, Math.round(finite(win.__parkourTasSnap?.subframes, TAS_SNAP_SUBFRAMES)));
  }

  function tasSnapDtEach() {
    return Math.max(0.0001, finite(win.__parkourTasSnap?.dtEach, TAS_SNAP_DT_EACH));
  }

  function tasSlowSubframes() {
    return Math.max(1, Math.round(finite(win.__parkourTasSnap?.slowSubframes, TAS_R_SLOW_SUBFRAMES)));
  }

  function tasSlowDtEach() {
    return Math.max(0.0001, finite(win.__parkourTasSnap?.slowDtEach, TAS_R_SLOW_DT_EACH));
  }

  function tasInputDt(v) {
    const cap = tasDtCapMs();
    return Math.max(0.1, Math.min(cap, finite(v, cap)));
  }

  function getVel(p) {
    const vx = p.vx ?? p.velocity?.x ?? p.vel?.x ?? 0;
    const vy = p.vy ?? p.velocity?.y ?? p.vel?.y ?? 0;
    const vz = p.vz ?? p.velocity?.z ?? p.vel?.z ?? 0;
    return { vx: finite(vx), vy: finite(vy), vz: finite(vz) };
  }

  function snapPlayer(p) {
    const v = getVel(p || {});
    return {
      x: round(finite(p?.x ?? p?.pos?.x), 4),
      y: round(finite(p?.y ?? p?.pos?.y), 4),
      z: round(finite(p?.z ?? p?.pos?.z), 4),
      vx: round(v.vx, 6),
      vy: round(v.vy, 6),
      vz: round(v.vz, 6),
      hVel: round(Math.hypot(v.vx, v.vz), 6),
      yaw: round(finite(p?.xDire ?? p?.xDir ?? p?.dir ?? p?.yaw), 6),
      pitch: round(finite(p?.yDire ?? p?.yDir), 6),
      onGround: !!p?.onGround,
      crouchVal: round(finite(p?.crouchVal), 6),
      slideTimer: round(finite(p?.slideTimer ?? p?.slideT), 6),
    };
  }

  function dist(a, b) {
    if (!a || !b) return Infinity;
    return Math.hypot(finite(a.x) - finite(b.x), finite(a.y) - finite(b.y), finite(a.z) - finite(b.z));
  }

  function xzDist(a, b) {
    if (!a || !b) return Infinity;
    return Math.hypot(finite(a.x) - finite(b.x), finite(a.z) - finite(b.z));
  }

  function normAngle(a) {
    while (a <= -Math.PI) a += Math.PI * 2;
    while (a > Math.PI) a -= Math.PI * 2;
    return a;
  }

  function getLocalPlayer() {
    return localPlayer || Game?.players?.list?.find?.(x => x.isYou) || null;
  }

  function startError(player, start) {
    const cur = snapPlayer(player);
    return {
      pos: cur,
      d3: dist(cur, start),
      dxz: xzDist(cur, start),
      dy: Math.abs(finite(cur.y) - finite(start?.y)),
      hVel: finite(cur.hVel),
    };
  }

  function startReady(player, start) {
    const e = startError(player, start);
    return e.dxz <= START_TOLERANCE && e.dy <= ALIGN_DONE_Y;
  }

  function clearActionInput(input) {
    if (!input) return;
    input[4] = -1;
    input[5] = 0;
    input[6] = 0;
    input[7] = 0;
    input[8] = 0;
    input[9] = 0;
    input[10] = 0;
    input[11] = 0;
    input[12] = 0;
    input[13] = 0;
    input[14] = 0;
  }

  function moveIndexToward(targetWorldAngle, yaw) {
    let bestI = -1;
    let bestErr = Infinity;
    for (let i = 0; i < MOVE_DIRS.length; i++) {
      const world = normAngle(MOVE_DIRS[i] - yaw);
      const err = Math.abs(normAngle(world - targetWorldAngle));
      if (err < bestErr) {
        bestErr = err;
        bestI = i;
      }
    }
    return bestI;
  }

  function normalizeRoute(obj) {
    const r = Array.isArray(obj) ? { frames: obj } : (obj || {});
    const f = Array.isArray(r.frames) ? r.frames : [];
    const out = f.filter(x => x && (x.input || x.in));
    let simT = 0;
    for (let i = 0; i < out.length; i++) {
      const frame = out[i];
      const src = frame.input || frame.in || [];
      const simDt = tasInputDt(finite(frame.simDt, finite(src[1], finite(frame.dt, TAS_DT_CAP_MS))));
      if (i === 0) {
        simT = finite(frame.simT, 0);
      } else {
        simT = Number.isFinite(frame.simT) ? frame.simT : simT + simDt;
      }
      frame.simDt = simDt;
      frame.simT = simT;
    }
    return { route: r, frames: out };
  }

  function loadRouteFile(file) {
    if (!file) return;
    const reader = new FileReader();
    reader.onload = () => {
      try {
        const loaded = normalizeRoute(JSON.parse(String(reader.result || '{}')));
        route = loaded.route;
        frames = loaded.frames;
        stopPlayback('loaded');
        lastStatus = 'loaded ' + frames.length + ' frames';
        paint();
      } catch (e) {
        console.error('[TASPlay] failed to load route json', e);
        route = null;
        frames = [];
        stopPlayback('load failed');
      }
    };
    reader.readAsText(file);
  }

  function frameState(frame) {
    return frame?.pre || frame?.state || frame?.s || null;
  }

  function setView(player, state) {
    if (!player || !state) return;
    const yaw = state.camYaw ?? state.yaw ?? state.xDire ?? state.dir;
    const pitch = state.camPitch ?? state.pitch ?? state.yDire;
    if (typeof yaw === 'number' && isFinite(yaw)) {
      player.xDire = yaw;
      player.xDir = yaw;
      player.xDirChase = yaw;
      if ('dir' in player) player.dir = yaw;
      if ('yaw' in player) player.yaw = yaw;
      const c = Game?.controls;
      if (c) {
        if (c.object?.rotation) c.object.rotation.y = yaw;
        c.xDr = yaw % (Math.PI * 2);
      }
    }
    if (typeof pitch === 'number' && isFinite(pitch)) {
      player.yDire = pitch;
      player.yDir = pitch;
      player.yDirChase = pitch;
      const c = Game?.controls;
      if (c) {
        if (c.pchObjc?.rotation) c.pchObjc.rotation.x = pitch;
        c.yDr = pitch % (Math.PI * 2);
      }
    }
  }

  function applyInput(input, frame) {
    const src = frame.input || frame.in || [];
    if (!input || !Array.isArray(src)) return;
    const liveSN = input[0];
    const liveDt = tasInputDt(input[1]);
    for (let i = 1; i < src.length; i++) {
      const v = src[i];
      input[i] = (v === null || v === undefined) ? 0 : v;
    }
    input[0] = liveSN;
    input[1] = cfg.recordedDt ? tasInputDt(finite(frame.simDt, finite(src[1], liveDt))) : liveDt;
    const state = frameState(frame);
    const yaw = state?.camYaw ?? state?.yaw;
    const pitch = state?.camPitch ?? state?.pitch;
    if (typeof pitch === 'number' && isFinite(pitch)) input[2] = Math.round(pitch * 1000);
    if (typeof yaw === 'number' && isFinite(yaw)) input[3] = Math.round(yaw * 1000);
  }

  function applyAlignInput(input, player) {
    if (!input || !player || !frames.length) return false;
    input[1] = tasInputDt(input[1]);
    const start = frameState(frames[0]);
    if (!start) {
      stopPlayback('no start frame');
      return false;
    }

    const e = startError(player, start);
    alignBest = Math.min(alignBest, e.dxz);
    if (performance.now() - alignStarted > ALIGN_TIMEOUT_MS) {
      stopPlayback('align timeout xz=' + e.dxz.toFixed(2));
      return false;
    }
    if (e.d3 > ALIGN_START_TOLERANCE + 4) {
      stopPlayback('align drifted ' + e.d3.toFixed(1) + 'u');
      return false;
    }

    setView(player, start);
    clearActionInput(input);
    const yaw = finite(start.camYaw ?? start.yaw ?? player.xDire);
    const pitch = finite(start.camPitch ?? start.pitch ?? player.yDire);
    input[2] = Math.round(pitch * 1000);
    input[3] = Math.round(yaw * 1000);

    if (e.dxz <= ALIGN_DONE_XZ && e.dy <= ALIGN_DONE_Y) {
      if (e.hVel <= ALIGN_SETTLE_HVEL) {
        aligning = false;
        setView(player, start);
        lastStatus = 'aligned - mouse4/5 start';
      } else {
        lastStatus = 'settling v=' + e.hVel.toFixed(3);
      }
      paint();
      return true;
    }

    const dx = finite(start.x) - finite(e.pos.x);
    const dz = finite(start.z) - finite(e.pos.z);
    const targetAng = Math.atan2(dz, dx);
    const moveIdx = moveIndexToward(targetAng, yaw);

    // Crouch-walk and pulse near the target. This is intentionally slow so the
    // first replay frame starts from the same spot instead of overshooting it.
    alignFrame++;
    let pulse = 1;
    if (e.dxz < 1.2 || e.hVel > 0.04) pulse = (alignFrame % 4 === 0) ? 1 : 0;
    else if (e.dxz < 2.8 || e.hVel > 0.03) pulse = (alignFrame % 2 === 0) ? 1 : 0;

    if (pulse && moveIdx >= 0) {
      input[4] = moveIdx;
      input[9] = 1;
    }
    lastStatus = 'align xz=' + e.dxz.toFixed(2) + ' best=' + alignBest.toFixed(2);
    paint();
    return true;
  }

  function advancePlayback(liveDt) {
    if (!cfg.timeSync) {
      playIndex++;
      return;
    }
    playElapsed += Math.max(0, finite(liveDt));
    while (playIndex + 1 < frames.length) {
      const nextT = finite(frames[playIndex + 1].simT, finite(frames[playIndex + 1].t)) - routeStartT;
      if (nextT > playElapsed + 0.001) break;
      playIndex++;
    }
  }

  function startPlayback() {
    if (!frames.length) {
      lastStatus = 'no route loaded';
      paint();
      return;
    }
    const p = getLocalPlayer();
    if (!p) {
      lastStatus = 'no local player';
      paint();
      return;
    }
    const start = frameState(frames[0]);
    const e = startError(p, start);
    if (!startReady(p, start)) {
      lastStatus = 'start off xz=' + e.dxz.toFixed(2) + ' y=' + e.dy.toFixed(2);
      paint();
      return;
    }
    localPlayer = p;
    aligning = false;
    playing = true;
    playIndex = 0;
    playElapsed = 0;
    routeStartT = finite(frames[0]?.simT, finite(frames[0]?.t));
    maxDrift = e.d3;
    lastStatus = 'playing';
    setView(p, start);
    paint();
  }

  function stopPlayback(reason = 'stopped') {
    playing = false;
    aligning = false;
    lastStatus = reason;
    paint();
  }

  function togglePlayback() {
    if (playing) stopPlayback();
    else if (aligning) stopPlayback('align stopped');
    else startPlayback();
  }

  function beginAlign() {
    if (!frames.length) {
      lastStatus = 'no route loaded';
      paint();
      return;
    }
    const p = getLocalPlayer();
    if (!p) {
      lastStatus = 'no local player';
      paint();
      return;
    }
    const start = frameState(frames[0]);
    const e = startError(p, start);
    if (e.d3 > ALIGN_START_TOLERANCE) {
      lastStatus = 'align too far: ' + e.d3.toFixed(1) + 'u';
      paint();
      return;
    }
    localPlayer = p;
    playing = false;
    aligning = true;
    alignStarted = performance.now();
    alignFrame = 0;
    alignBest = e.dxz;
    lastStatus = 'aligning xz=' + e.dxz.toFixed(2);
    paint();
  }

  function toggleAlign() {
    if (aligning) stopPlayback('align stopped');
    else if (!playing) beginAlign();
  }

  function hookPlayer(player) {
    if (!player || hookedPlayers.has(player)) return;
    hookedPlayers.add(player);
    if (player.isYou) localPlayer = player;

    const keys = Object.getOwnPropertyNames(player).filter(
      k => typeof player[k] === 'function' && player[k].length === 4
    );
    const procKey = keys[2];
    if (!procKey) return;

    const original = player[procKey];
    player[procKey] = function (input, game, recon, moveLock) {
      if (this.isYou) localPlayer = this;
      let expectedPost = null;
      let expectedPre = null;
      let liveDt = 0;
      if (this.isYou && aligning && input) {
        applyAlignInput(input, this);
      } else if (this.isYou && playing && input) {
        if (playIndex >= frames.length) {
          stopPlayback('done');
        } else {
          const frame = frames[playIndex];
          expectedPre = frameState(frame);
          expectedPost = frame.post || null;
          liveDt = finite(input[1]);
          const d = dist(snapPlayer(this), expectedPre);
          maxDrift = Math.max(maxDrift, d);
          if (d > cfg.hardDrift) {
            stopPlayback('hard desync ' + d.toFixed(1) + 'u');
          } else {
            setView(this, expectedPre);
            applyInput(input, frame);
          }
        }
      }

      const ret = original.call(this, input, game, recon, moveLock);

      if (this.isYou && playing && expectedPost) {
        const d2 = dist(snapPlayer(this), expectedPost);
        maxDrift = Math.max(maxDrift, d2);
        if (d2 > cfg.hardDrift) stopPlayback('hard desync ' + d2.toFixed(1) + 'u');
        else if (d2 > WARN_DRIFT) lastStatus = 'desync ' + d2.toFixed(1) + 'u';
        if (playing) advancePlayback(liveDt);
        if (playIndex >= frames.length) stopPlayback('done');
      }
      return ret;
    };
    console.log('[TASPlay] procInputs hooked');
  }

  function installPlayerHook() {
    const existing = Game?.players?.list?.find?.(p => p.isYou);
    if (existing) hookPlayer(existing);
    if (Game?.players?.add && !Game.players.__tasPlayAddHook) {
      const origAdd = Game.players.add;
      Game.players.add = function (...args) {
        const p = origAdd.call(this, ...args);
        if (p?.isYou) hookPlayer(p);
        return p;
      };
      Game.players.__tasPlayAddHook = true;
    }
  }

  function onGame(GUI, args) {
    const g = args && args[0];
    if (!g) return;
    Game = g;
    win._Game = g;
    buildGUI();
    installPlayerHook();
    paint();
  }

  function waitForBody(cb) {
    if (document.body) cb();
    else setTimeout(() => waitForBody(cb), 50);
  }

  function installGameCapture() {
    if (win._Game) {
      Game = win._Game;
      waitForBody(() => { buildGUI(); installPlayerHook(); paint(); });
      return;
    }
    if (win.__parkourTasGameHook) {
      win.__parkourTasGameHook.callbacks.push(onGame);
      return;
    }
    win.__parkourTasGameHook = { callbacks: [onGame] };
    Object.defineProperty(win, 'GUI', {
      configurable: true,
      enumerable: false,
      set: new Function('bus', 'return function(v){var a=[];try{a=arguments.callee.caller.arguments}catch(e){};try{delete this.GUI;this.GUI=v}catch(e){};for(var i=0;i<bus.callbacks.length;i++){try{bus.callbacks[i](v,a)}catch(_){}}}')(win.__parkourTasGameHook),
    });
  }

  let guiEls = null;

  function buildGUI() {
    if (document.getElementById('tas-play-gui')) return;
    const style = document.createElement('style');
    style.textContent = `
      #tas-play-gui{position:fixed;right:18px;top:118px;z-index:2147483647;font:12px/1.35 Consolas,monospace;color:#cbd5e1;user-select:none}
      #tas-play-panel{width:230px;background:rgba(5,8,12,.92);border:1px solid #a855f7;border-radius:7px;box-shadow:0 8px 28px rgba(0,0,0,.35);padding:10px}
      #tas-play-title{font-weight:700;color:#c084fc;text-align:center;letter-spacing:.8px;margin-bottom:8px}
      #tas-play-panel button,#tas-play-panel label{display:block;box-sizing:border-box;width:100%;margin:5px 0;padding:6px 7px;border-radius:5px;border:1px solid #334155;background:rgba(15,23,42,.75);color:#e2e8f0;text-align:center;cursor:pointer;font:12px Consolas,monospace}
      #tas-play-panel button:hover,#tas-play-panel label:hover{background:rgba(30,41,59,.95)}
      #tas-play-start.live{background:#14532d;border-color:#22c55e;color:#fff}
      #tas-play-load-label{border-color:#7e22ce;color:#e9d5ff}
      #tas-play-stats{margin-top:7px;color:#94a3b8;font-size:11px}
      #tas-play-stats b{color:#fff}
      #tas-play-hint{margin-top:5px;color:#64748b;font-size:10px}
    `;
    const box = document.createElement('div');
    box.id = 'tas-play-gui';
    box.innerHTML = `
      <div id="tas-play-panel">
        <div id="tas-play-title">PARKOUR TAS PLAYER</div>
        <label id="tas-play-load-label">LOAD ROUTE JSON<input id="tas-play-load" type="file" accept="application/json,.json" style="display:none"></label>
        <button id="tas-play-start">START</button>
        <button id="tas-play-stop">STOP</button>
        <div id="tas-play-stats">
          <div>state: <b data-k="state">boot</b></div>
          <div>frame: <b data-k="frame">0/0</b></div>
          <div>max drift: <b data-k="drift">0.0</b>u</div>
          <div>hard drift: <input data-k="hard" type="number" min="20" max="500" step="10"></div>
          <label id="tas-play-check"><input data-k="timesync" type="checkbox"> sim-time sync</label>
          <label id="tas-play-check"><input data-k="recdt" type="checkbox"> recorded dt</label>
          <div>R snap: <b data-k="snap">off</b></div>
          <div>clock: <b data-k="clock">20ms / q 33x1.1 / R 1x0.0033</b></div>
        </div>
        <div id="tas-play-hint">Default is strict frame replay. Press 0 within 10u to crouch-align. Mouse4/Mouse5 starts/stops.</div>
      </div>`;
    document.documentElement.appendChild(style);
    document.documentElement.appendChild(box);

    guiEls = {
      load: box.querySelector('#tas-play-load'),
      start: box.querySelector('#tas-play-start'),
      stop: box.querySelector('#tas-play-stop'),
      state: box.querySelector('[data-k="state"]'),
      frame: box.querySelector('[data-k="frame"]'),
      drift: box.querySelector('[data-k="drift"]'),
      hard: box.querySelector('[data-k="hard"]'),
      timeSync: box.querySelector('[data-k="timesync"]'),
      recDt: box.querySelector('[data-k="recdt"]'),
      snap: box.querySelector('[data-k="snap"]'),
      clock: box.querySelector('[data-k="clock"]'),
    };
    guiEls.load.addEventListener('change', e => loadRouteFile(e.target.files && e.target.files[0]));
    guiEls.start.addEventListener('click', startPlayback);
    guiEls.stop.addEventListener('click', () => stopPlayback());
    guiEls.hard.value = String(cfg.hardDrift);
    guiEls.timeSync.checked = !!cfg.timeSync;
    guiEls.recDt.checked = !!cfg.recordedDt;
    guiEls.hard.addEventListener('change', () => {
      cfg.hardDrift = Math.max(20, Math.min(500, parseFloat(guiEls.hard.value) || 100));
      guiEls.hard.value = String(cfg.hardDrift);
      saveCfg();
    });
    guiEls.timeSync.addEventListener('change', () => {
      cfg.timeSync = !!guiEls.timeSync.checked;
      saveCfg();
    });
    guiEls.recDt.addEventListener('change', () => {
      cfg.recordedDt = !!guiEls.recDt.checked;
      saveCfg();
    });
    paint();
    setInterval(paint, 100);
  }

  function paint() {
    if (!guiEls) return;
    guiEls.start.classList.toggle('live', playing || aligning);
    guiEls.start.textContent = playing ? 'PLAYING...' : aligning ? 'ALIGNING...' : 'START';
    guiEls.state.textContent = lastStatus;
    guiEls.frame.textContent = playIndex + '/' + frames.length;
    guiEls.drift.textContent = maxDrift.toFixed(1);
    guiEls.hard.value = String(cfg.hardDrift);
    guiEls.timeSync.checked = !!cfg.timeSync;
    guiEls.recDt.checked = !!cfg.recordedDt;
    guiEls.snap.textContent = win.__parkourTasSnap?.held ? 'on' : 'off';
    guiEls.clock.textContent = `${tasDtCapMs()}ms / q ${tasSnapSubframes()}x${tasSnapDtEach()} / R ${tasSlowSubframes()}x${tasSlowDtEach()}`;
  }

  function installMouseButtons() {
    window.addEventListener('mousedown', e => {
      if (e.button === 3 || e.button === 4) {
        e.preventDefault();
        e.stopPropagation();
        togglePlayback();
      }
    }, true);
  }

  function isTypingTarget(el) {
    const tag = String(el?.tagName || '').toLowerCase();
    return tag === 'input' || tag === 'textarea' || tag === 'select' || !!el?.isContentEditable;
  }

  function installAlignKey() {
    window.addEventListener('keydown', e => {
      if (e.repeat || isTypingTarget(e.target)) return;
      if (e.code === 'Digit0' || e.code === 'Numpad0' || e.key === '0') {
        e.preventDefault();
        e.stopPropagation();
        toggleAlign();
      }
    }, true);
  }

  function installRSnap() {
    const S = win.__parkourTasSnap = win.__parkourTasSnap || { held: false };
    if (!Number.isFinite(Number(S.subframes))) S.subframes = TAS_SNAP_SUBFRAMES;
    if (!Number.isFinite(Number(S.dtEach))) S.dtEach = TAS_SNAP_DT_EACH;
    if (!Number.isFinite(Number(S.dtCapMs))) S.dtCapMs = TAS_DT_CAP_MS;
    if (!Number.isFinite(Number(S.slowSubframes))) S.slowSubframes = TAS_R_SLOW_SUBFRAMES;
    if (!Number.isFinite(Number(S.slowDtEach))) S.slowDtEach = TAS_R_SLOW_DT_EACH;
    function hold(v) {
      S.held = !!v;
      paint();
    }
    window.addEventListener('keydown', e => {
      if ((e.code === 'KeyR' || String(e.key).toLowerCase() === 'r') && !e.repeat) hold(true);
    }, true);
    window.addEventListener('keyup', e => {
      if (e.code === 'KeyR' || String(e.key).toLowerCase() === 'r') hold(false);
    }, true);
    if (win.__parkourTasSnapWS) return;
    win.__parkourTasSnapWS = true;
    const src = `(()=>{if(window.__parkourTasSnapWSPage)return;window.__parkourTasSnapWSPage=1;const enc=n=>[(n>>4)&15,n&15],ah=b=>((b[b.length-2]<<4)|b[b.length-1]),u=d=>d instanceof ArrayBuffer?new Uint8Array(d):ArrayBuffer.isView(d)?new Uint8Array(d.buffer,d.byteOffset,d.byteLength):null;function pack(m,a){const p=window.msgpack&&window.msgpack.encode?window.msgpack.encode(m):null;if(!p)return null;const b=new Uint8Array(p.length+2);b.set(p,0);b.set(enc(a),b.length-2);return b}function dec(d){try{const b=u(d);if(!b||b.length<3||!window.msgpack)return null;const m=window.msgpack.decode(b.slice(0,b.length-2));return Array.isArray(m)&&m[0]==='q'?{m,a:ah(b)}:null}catch(e){return null}}function dts(n,e){n=Math.max(1,Math.round(Number(n)||1));e=Number(e)||0.0001;const a=[];for(let i=0;i<n;i++)a.push(e);return a}function qdts(S){return S&&S.held?dts(S.slowSubframes||${TAS_R_SLOW_SUBFRAMES},S.slowDtEach||${TAS_R_SLOW_DT_EACH}):dts(S&&S.subframes||${TAS_SNAP_SUBFRAMES},S&&S.dtEach||${TAS_SNAP_DT_EACH})}const O=window.WebSocket;window.WebSocket=new Proxy(O,{construct(T,A){const w=new T(...A),s=w.send;w.send=function(d){const r=dec(d);if(r){const S=window.__parkourTasSnap||{};const m=r.m.slice();m[3]=qdts(S);const b=pack(m,(r.a+37)&255);if(b)return s.call(this,b)}return s.call(this,d)};return w}})})();`;
    const s = document.createElement('script');
    s.textContent = src;
    (document.head || document.documentElement).appendChild(s);
    s.remove();
  }

  win.__parkourTasPlayer = {
    get route() { return route; },
    get frames() { return frames; },
    get playing() { return playing; },
    get aligning() { return aligning; },
    start: startPlayback,
    stop: stopPlayback,
    align: beginAlign,
    loadObject(obj) {
      const loaded = normalizeRoute(obj);
      route = loaded.route;
      frames = loaded.frames;
      stopPlayback('loaded');
    },
  };

  installRSnap();
  installMouseButtons();
  installAlignKey();
  installGameCapture();
})();
