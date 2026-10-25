// ==UserScript==
// @name         Krunker Parkour TAS Recorder
// @namespace    local.krunker.parkour.tas
// @version      1.0.3
// @description  Records per-procInputs input/state frames for segmented parkour TAS routes.
// @match        https://krunker.io/*
// @match        https://*.browserfps.com/*
// @run-at       document-start
// @grant        unsafeWindow
// ==/UserScript==

(function () {
  'use strict';

  const win = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
  const SCRIPT = 'TASRec';
  const MAX_FRAMES = 500000;
  const TAS_DT_CAP_MS = 30;
  const TAS_SNAP_SUBFRAMES = 30;
  const TAS_SNAP_DT_EACH = 1.1;
  const TAS_R_SLOW_SUBFRAMES = 1;
  const TAS_R_SLOW_DT_EACH = 0.0033;
  const SPEEDBUILD_HOLD_MS = 180;
  const SPEEDBUILD_PRE_CROUCH_MS = 100;
  const SPEEDBUILD_GROUND_SLIDE_MS = 80;
  const AUTO_BHOP_PRE_CROUCH_MS = 40;
  const AUTO_BHOP_GROUND_SLIDE_MS = 30;
  const GRAVITY = 0.00015;
  const RISE_DECEL = 0.000032;
  const TERMINAL_VEL_Y = -0.3;
  const JUMP_VEL_BASE = 0.072;
  const JUMP_PUSH = 0.1;
  const GROUND_DECEL = 0.99;
  const AIR_DECEL = 0.9996;
  const VEL_DECEL_MIN = 0.0001;
  const CROUCH_JUMP_PEN = 0.25;
  const SIM_STEPS = 220;
  const SIM_DT = 6;
  const ARC_TUBE_WIDTH = 12;
  const LAND_WORLD_RADIUS = 3.2;
  const ARC1_COLOR = '#00ff88';
  const ARC2_COLOR = '#00aaff';
  const PRE_COLOR = '#00ccff';
  const LAND1_COLOR = '#ff3333';
  const LAND2_COLOR = '#ffaa00';

  const INPUT_INDEX = {
    dt: 1,
    pitch: 2,
    yaw: 3,
    moveDir: 4,
    shoot: 5,
    scope: 6,
    jump: 7,
    reload: 8,
    crouch: 9,
  };
  const MOVE_FORWARD = 1;

  let Game = null;
  let localPlayer = null;
  const hookedPlayers = new WeakSet();
  let arcCanvas = null;
  let arcCtx = null;
  let arcRaf = 0;
  let lastArcPreview = null;

  let recording = false;
  let recordStartRealMs = 0;
  let recordBaseRouteMs = 0;
  let recordBaseSimMs = 0;
  let recordSimMs = 0;
  let activeSegment = null;
  let lastStatus = 'boot';
  const MOVE_DIRS = [];
  for (let i = 0; i < 8; i++) MOVE_DIRS.push(-Math.PI + (i + 1) * Math.PI / 4);
  const macro = {
    holdDown: false,
    holdStarted: 0,
    speedBuild: false,
    autoBhop: false,
    legYaw: 0,
    turned: false,
    airMs: 0,
    lastAirMs: 0,
    predGroundMs: Infinity,
    groundMs: 999,
    wasGround: false,
  };

  function nowMs() {
    return performance.now();
  }

  function finite(v, fallback = 0) {
    return (typeof v === 'number' && isFinite(v)) ? v : fallback;
  }

  function round(v, d = 4) {
    if (typeof v !== 'number' || !isFinite(v)) return 0;
    const m = Math.pow(10, d);
    return Math.round(v * m) / m;
  }

  function normAngle(a) {
    while (a <= -Math.PI) a += Math.PI * 2;
    while (a > Math.PI) a -= Math.PI * 2;
    return a;
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

  function tasClock() {
    return {
      dtCapMs: tasDtCapMs(),
      snapSubframes: tasSnapSubframes(),
      snapDtEach: tasSnapDtEach(),
      rSlowSubframes: tasSlowSubframes(),
      rSlowDtEach: tasSlowDtEach(),
    };
  }

  function getVel(p) {
    const vx = p.vx ?? p.velocity?.x ?? p.vel?.x ?? 0;
    const vy = p.vy ?? p.velocity?.y ?? p.vel?.y ?? 0;
    const vz = p.vz ?? p.velocity?.z ?? p.vel?.z ?? 0;
    return { vx: finite(vx), vy: finite(vy), vz: finite(vz) };
  }

  function getGroundY(x, y, z) {
    try {
      const coll = Game?.map?.collisions;
      if (!coll) return null;
      if (typeof coll.rayCast === 'function') {
        const hit = coll.rayCast(x, y + 1, z, x, y - 200, z);
        if (hit) return hit.y;
      }
      if (typeof coll.getHeight === 'function') return coll.getHeight(x, z);
    } catch {}
    return null;
  }

  function simulateArc(p, inputArr, startVelOverride) {
    const state = {
      x: p.x ?? p.pos?.x ?? 0,
      y: p.y ?? p.pos?.y ?? 0,
      z: p.z ?? p.pos?.z ?? 0,
      vx: startVelOverride?.vx ?? p.vx ?? p.velocity?.x ?? p.vel?.x ?? 0,
      vy: startVelOverride?.vy ?? p.vy ?? p.velocity?.y ?? p.vel?.y ?? 0,
      vz: startVelOverride?.vz ?? p.vz ?? p.velocity?.z ?? p.vel?.z ?? 0,
      xDire: p.xDire ?? p.xDir ?? p.yDire ?? p.yDir ?? 0,
      crouchVal: p.crouchVal ?? 0,
      onGround: p.onGround ?? false,
      aimVal: p.aimVal ?? 0,
    };

    if (startVelOverride?.x !== undefined) {
      state.x = startVelOverride.x;
      state.y = startVelOverride.y;
      state.z = startVelOverride.z;
      state.onGround = true;
    }

    const jumpPressed = !!(inputArr?.[INPUT_INDEX.jump]);
    const dt = SIM_DT;
    const points = [];

    for (let i = 0; i < SIM_STEPS; i++) {
      points.push({
        x: state.x, y: state.y, z: state.z,
        vx: state.vx, vy: state.vy, vz: state.vz,
      });

      if (i === 0 && jumpPressed && state.onGround) {
        let jv = JUMP_VEL_BASE * (1 - CROUCH_JUMP_PEN * state.crouchVal);
        if (state.aimVal < 1) jv *= 0.85;
        state.vy = jv;
        const hSpeed = Math.sqrt(state.vx * state.vx + state.vz * state.vz);
        state.vx -= JUMP_PUSH * hSpeed * Math.sin(state.xDire);
        state.vz -= JUMP_PUSH * hSpeed * Math.cos(state.xDire);
        state.onGround = false;
      }

      state.vy -= GRAVITY * dt;
      if (state.vy > 0) state.vy -= RISE_DECEL * dt;
      if (state.vy < TERMINAL_VEL_Y) state.vy = TERMINAL_VEL_Y;

      const df = Math.pow(state.onGround ? GROUND_DECEL : AIR_DECEL, dt);
      state.vx *= df;
      state.vz *= df;
      if (Math.abs(state.vx) < VEL_DECEL_MIN) state.vx = 0;
      if (Math.abs(state.vz) < VEL_DECEL_MIN) state.vz = 0;

      state.x += state.vx * dt;
      state.y += state.vy * dt;
      state.z += state.vz * dt;

      if (!state.onGround && state.vy <= 0) {
        const groundY = getGroundY(state.x, state.y, state.z) ?? 0;
        if (state.y <= groundY + 0.1) {
          state.y = groundY;
          state.vy = 0;
          state.onGround = true;
        }
      }
    }

    return { points, finalState: state };
  }

  function findLandingIdx(points) {
    for (let i = 1; i < points.length; i++) {
      const p = points[i];
      const groundY = getGroundY(p.x, p.y, p.z) ?? 0;
      if (p.y <= groundY + 0.3 && p.y <= points[i - 1].y) return i;
    }
    return points.length - 1;
  }

  function predictLandingMs(p, input) {
    if (!p || p.onGround) return 0;
    const sim = simulateArc(p, input || []);
    const idx = findLandingIdx(sim.points);
    const landing = sim.points[idx];
    const groundY = landing ? getGroundY(landing.x, landing.y, landing.z) : null;
    if (idx >= sim.points.length - 1 && (groundY == null || landing.y > groundY + 0.3)) return Infinity;
    return idx * SIM_DT;
  }

  function findApexIdx(points) {
    let maxY = -Infinity;
    let idx = 0;
    for (let i = 0; i < points.length; i++) {
      if (points[i].y > maxY) {
        maxY = points[i].y;
        idx = i;
      }
    }
    return idx;
  }

  function createArcCanvas() {
    if (arcCanvas || !document.body) return;
    arcCanvas = document.createElement('canvas');
    arcCanvas.id = 'tas-rec-arc';
    arcCanvas.style.cssText = 'position:fixed;inset:0;width:100%;height:100%;z-index:9998;pointer-events:none';
    document.body.appendChild(arcCanvas);
    arcCtx = arcCanvas.getContext('2d');
    const resize = () => {
      if (!arcCanvas) return;
      arcCanvas.width = window.innerWidth;
      arcCanvas.height = window.innerHeight;
    };
    window.addEventListener('resize', resize);
    resize();
  }

  function worldToScreen(wx, wy, wz) {
    try {
      const cam = Game?.render?.fpsCamera ?? Game?.render?.camera;
      if (!cam || !arcCanvas) return null;
      const T = win.THREE || Game?.THREE || Game?.render?.THREE;
      if (T?.Vector3 && typeof T.Vector3 === 'function') {
        const v = new T.Vector3(wx, wy, wz);
        cam.updateMatrixWorld?.();
        v.project(cam);
        if (v.z < -1 || v.z > 1 || v.x < -1.25 || v.x > 1.25 || v.y < -1.25 || v.y > 1.25) return null;
        return { x: (v.x + 1) * 0.5 * arcCanvas.width, y: (-v.y + 1) * 0.5 * arcCanvas.height, depth: Math.max(0.1, Math.abs(v.z)) };
      }

      cam.updateMatrixWorld?.();
      cam.updateMatrixWorldInverse?.();
      const me = cam.matrixWorldInverse?.elements;
      const pe = cam.projectionMatrix?.elements;
      if (!me || !pe) return null;
      const vx = me[0] * wx + me[4] * wy + me[8] * wz + me[12];
      const vy = me[1] * wx + me[5] * wy + me[9] * wz + me[13];
      const vz = me[2] * wx + me[6] * wy + me[10] * wz + me[14];
      const vw = me[3] * wx + me[7] * wy + me[11] * wz + me[15];
      const cx = pe[0] * vx + pe[4] * vy + pe[8] * vz + pe[12] * vw;
      const cy = pe[1] * vx + pe[5] * vy + pe[9] * vz + pe[13] * vw;
      const cz = pe[2] * vx + pe[6] * vy + pe[10] * vz + pe[14] * vw;
      const cw = pe[3] * vx + pe[7] * vy + pe[11] * vz + pe[15] * vw;
      if (Math.abs(cw) < 1e-6) return null;
      const nx = cx / cw;
      const ny = cy / cw;
      const nz = cz / cw;
      if (nz < -1 || nz > 1 || nx < -1.25 || nx > 1.25 || ny < -1.25 || ny > 1.25) return null;
      return { x: (nx + 1) * 0.5 * arcCanvas.width, y: (-ny + 1) * 0.5 * arcCanvas.height, depth: Math.max(0.1, Math.abs(cw)) };
    } catch {
      return null;
    }
  }

  function drawProjectedLine(screenPts, color, alpha, width) {
    if (!arcCtx) return;
    arcCtx.save();
    arcCtx.lineJoin = 'round';
    arcCtx.lineCap = 'round';
    const layers = [
      { w: width * 5.5, a: 0.05 },
      { w: width * 3.0, a: 0.12 },
      { w: width * 1.4, a: 0.45 },
      { w: width * 0.45, a: 1.0 },
    ];
    for (const layer of layers) {
      arcCtx.globalAlpha = alpha * layer.a;
      arcCtx.strokeStyle = color;
      arcCtx.lineWidth = layer.w;
      arcCtx.beginPath();
      let started = false;
      for (const sp of screenPts) {
        if (!sp) {
          started = false;
          continue;
        }
        if (!started) {
          arcCtx.moveTo(sp.x, sp.y);
          started = true;
        } else {
          arcCtx.lineTo(sp.x, sp.y);
        }
      }
      arcCtx.stroke();
    }
    arcCtx.restore();
  }

  function drawArc3D(worldPts, color, alpha) {
    if (!arcCtx || !worldPts?.length) return;
    const screenPts = worldPts.map(p => worldToScreen(p.x, p.y, p.z));
    const shadowPts = worldPts.map(p => {
      const gy = getGroundY(p.x, p.y, p.z);
      return gy == null ? null : worldToScreen(p.x, gy + 0.04, p.z);
    });

    arcCtx.save();
    arcCtx.setLineDash([4, 7]);
    arcCtx.globalAlpha = alpha * 0.25;
    arcCtx.strokeStyle = color;
    arcCtx.lineWidth = 2;
    arcCtx.beginPath();
    let started = false;
    for (const sp of shadowPts) {
      if (!sp) {
        started = false;
        continue;
      }
      if (!started) {
        arcCtx.moveTo(sp.x, sp.y);
        started = true;
      } else {
        arcCtx.lineTo(sp.x, sp.y);
      }
    }
    arcCtx.stroke();
    arcCtx.setLineDash([]);

    for (let i = 0; i < screenPts.length; i += 16) {
      const sp = screenPts[i];
      const sh = shadowPts[i];
      if (!sp || !sh) continue;
      arcCtx.globalAlpha = alpha * 0.18;
      arcCtx.strokeStyle = color;
      arcCtx.lineWidth = 1;
      arcCtx.setLineDash([2, 5]);
      arcCtx.beginPath();
      arcCtx.moveTo(sp.x, sp.y);
      arcCtx.lineTo(sh.x, sh.y);
      arcCtx.stroke();
      arcCtx.setLineDash([]);
    }
    arcCtx.restore();

    drawProjectedLine(screenPts, color, alpha, ARC_TUBE_WIDTH);

    arcCtx.save();
    for (let i = 0; i < screenPts.length; i += 16) {
      const sp = screenPts[i];
      if (!sp) continue;
      arcCtx.globalAlpha = alpha * 0.52;
      arcCtx.fillStyle = color;
      arcCtx.beginPath();
      arcCtx.arc(sp.x, sp.y, 3.2, 0, Math.PI * 2);
      arcCtx.fill();
      arcCtx.globalAlpha = alpha * 0.9;
      arcCtx.fillStyle = '#ffffff';
      arcCtx.beginPath();
      arcCtx.arc(sp.x, sp.y, 1.2, 0, Math.PI * 2);
      arcCtx.fill();
    }

    const ap = screenPts[findApexIdx(worldPts)];
    if (ap) {
      arcCtx.globalAlpha = alpha * 0.65;
      arcCtx.strokeStyle = '#ffffff';
      arcCtx.lineWidth = 2;
      arcCtx.beginPath();
      arcCtx.arc(ap.x, ap.y, ARC_TUBE_WIDTH * 1.15, 0, Math.PI * 2);
      arcCtx.stroke();
    }
    arcCtx.restore();
  }

  function drawWorldRing(points, color, alpha, width = 2.5) {
    if (!arcCtx || points.length < 2) return;
    const screenPts = points.map(p => worldToScreen(p.x, p.y, p.z));
    arcCtx.save();
    arcCtx.strokeStyle = color;
    arcCtx.lineWidth = width;
    arcCtx.globalAlpha = alpha;
    arcCtx.beginPath();
    let started = false;
    for (const sp of screenPts) {
      if (!sp) {
        started = false;
        continue;
      }
      if (!started) {
        arcCtx.moveTo(sp.x, sp.y);
        started = true;
      } else {
        arcCtx.lineTo(sp.x, sp.y);
      }
    }
    arcCtx.closePath();
    arcCtx.stroke();
    arcCtx.restore();
  }

  function drawLanding(landPt, color, label) {
    if (!arcCtx || !landPt) return;
    const gy = getGroundY(landPt.x, landPt.y, landPt.z);
    const y = (gy == null ? landPt.y : gy) + 0.08;
    const ring = [];
    for (let i = 0; i <= 40; i++) {
      const a = i / 40 * Math.PI * 2;
      ring.push({
        x: landPt.x + Math.cos(a) * LAND_WORLD_RADIUS,
        y,
        z: landPt.z + Math.sin(a) * LAND_WORLD_RADIUS,
      });
    }
    drawWorldRing(ring, color, 0.95, 3);

    const sp = worldToScreen(landPt.x, y, landPt.z);
    if (!sp) return;
    arcCtx.save();
    arcCtx.strokeStyle = color;
    arcCtx.fillStyle = color;
    arcCtx.globalAlpha = 0.9;
    arcCtx.lineWidth = 1.5;
    const r = 18;
    arcCtx.beginPath();
    arcCtx.moveTo(sp.x - r, sp.y);
    arcCtx.lineTo(sp.x + r, sp.y);
    arcCtx.moveTo(sp.x, sp.y - r);
    arcCtx.lineTo(sp.x, sp.y + r);
    arcCtx.stroke();
    if (label) {
      arcCtx.font = 'bold 11px monospace';
      arcCtx.fillText(label, sp.x + 18, sp.y - 8);
    }
    arcCtx.restore();
  }

  function updateArcPreview(player, inputArr) {
    if (!player || !inputArr) return;
    const inAir = !player.onGround;
    const firstInput = Array.prototype.slice.call(inputArr);
    const fakeJump = !inAir && !firstInput[INPUT_INDEX.jump];
    if (fakeJump) firstInput[INPUT_INDEX.jump] = 1;

    const sim1 = simulateArc(player, firstInput);
    const li1 = findLandingIdx(sim1.points);
    const land1 = sim1.points[li1];
    const arc1 = sim1.points.slice(0, li1 + 1);
    let arc2 = [];
    let land2 = null;
    if (li1 < sim1.points.length - 5 && land1) {
      const secondInput = firstInput.slice();
      secondInput[INPUT_INDEX.jump] = 1;
      const sim2 = simulateArc(player, secondInput, {
        x: land1.x,
        y: getGroundY(land1.x, land1.y, land1.z) ?? land1.y,
        z: land1.z,
        vx: land1.vx,
        vy: 0,
        vz: land1.vz,
      });
      const li2 = findLandingIdx(sim2.points);
      land2 = sim2.points[li2];
      arc2 = sim2.points.slice(0, li2 + 1);
    }

    lastArcPreview = {
      arc1,
      arc2,
      land1,
      land2,
      fakeJump,
      actualFirst: inAir || !!inputArr[INPUT_INDEX.jump],
    };
  }

  function drawArcPreviewLoop() {
    arcRaf = requestAnimationFrame(drawArcPreviewLoop);
    if (!arcCanvas || !arcCtx) return;
    arcCtx.clearRect(0, 0, arcCanvas.width, arcCanvas.height);
    const a = lastArcPreview;
    if (!a) return;
    drawArc3D(a.arc1, a.fakeJump ? PRE_COLOR : ARC1_COLOR, a.actualFirst ? 0.9 : 0.7);
    drawLanding(a.land1, LAND1_COLOR, a.fakeJump ? 'LAND?' : 'LAND');
    if (a.arc2?.length) {
      drawArc3D(a.arc2, ARC2_COLOR, 0.55);
      drawLanding(a.land2, LAND2_COLOR, 'NEXT');
    }
  }

  function startArcVisualizer() {
    createArcCanvas();
    if (!arcRaf) drawArcPreviewLoop();
  }

  function setViewYaw(p, yaw, input) {
    yaw = normAngle(yaw);
    if (!p) return yaw;
    if (input) input[INPUT_INDEX.yaw] = Math.round(yaw * 1000);
    p.xDire = yaw;
    p.xDir = yaw;
    if ('dir' in p) p.dir = yaw;
    if ('yaw' in p) p.yaw = yaw;
    const c = Game?.controls;
    if (c) {
      if (c.object?.rotation) c.object.rotation.y = yaw;
      c.xDr = yaw % (Math.PI * 2);
    }
    return yaw;
  }

  function releaseViewRig(p) {
    if (!p) return;
    const yaw = normAngle(finite(Game?.controls?.xDr ?? p.xDire ?? p.xDir ?? macro.legYaw, 0));
    p.xDire = yaw;
    p.xDir = yaw;
    if ('dir' in p) p.dir = yaw;
    if ('yaw' in p) p.yaw = yaw;
    // These are normally null on the local player. Leaving a forced chase value
    // behind can desync the first-person weapon/hands from the camera for a few ticks.
    if ('xDirChase' in p) p.xDirChase = null;
    if ('yDirChase' in p) p.yDirChase = null;
    const c = Game?.controls;
    if (c) {
      if (c.object?.rotation) c.object.rotation.y = yaw;
      c.xDr = yaw % (Math.PI * 2);
    }
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

  function clearMacroEdges(input) {
    input[INPUT_INDEX.jump] = 0;
    input[INPUT_INDEX.crouch] = 0;
  }

  function updateMacroClock(p, dt) {
    const onGround = !!p?.onGround;
    if (onGround) {
      if (!macro.wasGround) {
        if (macro.airMs > SPEEDBUILD_PRE_CROUCH_MS) macro.lastAirMs = macro.airMs;
        macro.airMs = 0;
        macro.groundMs = 0;
      } else {
        macro.groundMs += dt;
      }
    } else {
      if (macro.wasGround) macro.airMs = 0;
      macro.airMs += dt;
    }
    macro.wasGround = onGround;
    return onGround;
  }

  function shouldPreCrouch(p, preCrouchMs, input) {
    if (p?.onGround) return false;
    const v = getVel(p || {});
    const landMs = predictLandingMs(p, input);
    macro.predGroundMs = landMs;
    if (Number.isFinite(landMs)) return landMs <= preCrouchMs;
    if (macro.lastAirMs > preCrouchMs * 2) {
      return macro.airMs >= macro.lastAirMs - preCrouchMs;
    }
    return macro.airMs >= preCrouchMs && v.vy < -0.055;
  }

  function beginSpeedBuild(p) {
    macro.speedBuild = true;
    macro.turned = false;
    macro.airMs = 0;
    macro.groundMs = 999;
    macro.wasGround = !!p?.onGround;
    macro.legYaw = normAngle(finite(Game?.controls?.xDr ?? p?.xDire ?? p?.xDir ?? p?.dir ?? p?.yaw, 0));
    lastStatus = 'speedbuild';
  }

  function stopSpeedBuild() {
    if (macro.speedBuild) releaseViewRig(localPlayer);
    macro.speedBuild = false;
    macro.turned = false;
    lastStatus = recording ? (macro.autoBhop ? 'auto bhop' : 'recording') : lastStatus;
  }

  function toggleAutoBhop() {
    macro.autoBhop = !macro.autoBhop;
    if (macro.autoBhop) stopSpeedBuild();
    lastStatus = macro.autoBhop ? 'auto bhop on' : 'auto bhop off';
    paint();
  }

  function resetMacroRun() {
    macro.speedBuild = false;
    macro.turned = false;
    macro.airMs = 0;
    macro.lastAirMs = 0;
    macro.groundMs = 999;
    macro.wasGround = !!localPlayer?.onGround;
  }

  function maybeArmSpeedBuild(p) {
    if (!recording || macro.autoBhop || macro.speedBuild || !macro.holdDown) return;
    if (nowMs() - macro.holdStarted >= SPEEDBUILD_HOLD_MS) beginSpeedBuild(p);
  }

  function applySpeedBuildInput(input, p, dt) {
    const onGround = updateMacroClock(p, dt);
    clearMacroEdges(input);
    if (!onGround && shouldPreCrouch(p, SPEEDBUILD_PRE_CROUCH_MS, input) && !macro.turned) {
      macro.legYaw = normAngle(macro.legYaw + Math.PI);
      macro.turned = true;
    }
    setViewYaw(p, macro.legYaw, input);
    input[INPUT_INDEX.moveDir] = MOVE_FORWARD;

    if (onGround) {
      input[INPUT_INDEX.crouch] = macro.groundMs < SPEEDBUILD_GROUND_SLIDE_MS ? 1 : 0;
      if (macro.groundMs >= SPEEDBUILD_GROUND_SLIDE_MS) {
        input[INPUT_INDEX.jump] = 1;
        macro.groundMs = 0;
        macro.turned = false;
      }
    } else if (shouldPreCrouch(p, SPEEDBUILD_PRE_CROUCH_MS, input)) {
      input[INPUT_INDEX.crouch] = 1;
    }
  }

  function applyAutoBhopInput(input, p, dt) {
    const onGround = updateMacroClock(p, dt);
    clearMacroEdges(input);
    if (onGround) {
      input[INPUT_INDEX.crouch] = macro.groundMs < AUTO_BHOP_GROUND_SLIDE_MS ? 1 : 0;
      if (macro.groundMs >= AUTO_BHOP_GROUND_SLIDE_MS) {
        input[INPUT_INDEX.jump] = 1;
        macro.groundMs = 0;
      }
    } else if (shouldPreCrouch(p, AUTO_BHOP_PRE_CROUCH_MS, input)) {
      input[INPUT_INDEX.crouch] = 1;
    }
  }

  function applyRecorderMacros(input, p) {
    if (!input || !recording) return;
    const dt = tasInputDt(input[INPUT_INDEX.dt]);
    maybeArmSpeedBuild(p);
    if (macro.speedBuild) applySpeedBuildInput(input, p, dt);
    else if (macro.autoBhop) applyAutoBhopInput(input, p, dt);
    else updateMacroClock(p, dt);
  }

  function snapPlayer(p) {
    const v = getVel(p || {});
    const yaw = finite(p?.xDire ?? p?.xDir ?? p?.dir ?? p?.yaw);
    const pitch = finite(p?.yDire ?? p?.yDir ?? 0);
    const c = Game?.controls || null;
    return {
      x: round(finite(p?.x ?? p?.pos?.x), 4),
      y: round(finite(p?.y ?? p?.pos?.y), 4),
      z: round(finite(p?.z ?? p?.pos?.z), 4),
      vx: round(v.vx, 6),
      vy: round(v.vy, 6),
      vz: round(v.vz, 6),
      hVel: round(Math.hypot(v.vx, v.vz), 6),
      yaw: round(yaw, 6),
      pitch: round(pitch, 6),
      camYaw: round(finite(c?.xDr ?? c?.object?.rotation?.y, yaw), 6),
      camPitch: round(finite(c?.yDr ?? c?.pchObjc?.rotation?.x, pitch), 6),
      dir: round(finite(p?.dir), 6),
      aimVal: round(finite(p?.aimVal), 6),
      onGround: !!p?.onGround,
      onTerrain: !!p?.onTerrain,
      onLadder: !!p?.onLadder,
      onPad: !!p?.onPad,
      onWall: finite(p?.onWall),
      crouchVal: round(finite(p?.crouchVal), 6),
      slideTimer: round(finite(p?.slideTimer ?? p?.slideT), 6),
      canSlide: !!p?.canSlide,
      didJump: !!p?.didJump,
      didJumpW: !!p?.didJumpW,
      inputSN: finite(p?.inputSN),
      health: finite(p?.health),
      weaponIndex: finite(p?.weaponIndex ?? p?.weapon?.id, -1),
    };
  }

  function cleanInput(input) {
    if (!input) return [];
    const a = Array.prototype.slice.call(input);
    return a.map(v => {
      if (v === undefined) return null;
      if (typeof v === 'number') return isFinite(v) ? round(v, 6) : 0;
      if (typeof v === 'boolean' || v === null || typeof v === 'string') return v;
      return v ? 1 : 0;
    });
  }

  function flatConfig() {
    const cfg = Game?.config || {};
    const out = {};
    for (const k in cfg) {
      const v = cfg[k];
      if (typeof v === 'number' || typeof v === 'boolean' || typeof v === 'string') out[k] = v;
    }
    return out;
  }

  function newRoute() {
    return {
      type: 'krunker-parkour-tas-route',
      version: 1,
      source: 'procInputs',
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
      inputIndex: INPUT_INDEX,
      meta: {
        game: 'krunker',
        note: 'Input-level TAS route. Replay uses procInputs frames plus recorded yaw/pitch. No websocket packet replay.',
        sample: 'one frame per local-player procInputs call',
        tasClock: tasClock(),
      },
      segments: [],
      frames: [],
    };
  }

  let route = newRoute();

  function normalizeLoadedRoute(obj) {
    if (Array.isArray(obj)) {
      const r = newRoute();
      r.frames = obj;
      r.segments = [{ index: 0, startFrame: 0, endFrame: Math.max(0, obj.length - 1), loadedArray: true }];
      return r;
    }
    const r = obj && typeof obj === 'object' ? obj : newRoute();
    if (!Array.isArray(r.frames)) r.frames = [];
    if (!Array.isArray(r.segments)) r.segments = [];
    if (!r.type) r.type = 'krunker-parkour-tas-route';
    if (!r.version) r.version = 1;
    if (!r.inputIndex) r.inputIndex = INPUT_INDEX;
    if (!r.meta) r.meta = {};
    return r;
  }

  function lastFrame() {
    return route.frames.length ? route.frames[route.frames.length - 1] : null;
  }

  function startRecording() {
    if (recording) return;
    if (!route || !Array.isArray(route.frames)) route = newRoute();
    resetMacroRun();
    const last = lastFrame();
    recordBaseRouteMs = last ? finite(last.t) + Math.max(0.1, finite(last.dt, 16)) : 0;
    recordBaseSimMs = last ? finite(last.simT, finite(last.t)) + tasInputDt(finite(last.simDt, finite(last.input?.[1], TAS_DT_CAP_MS))) : 0;
    recordSimMs = recordBaseSimMs;
    recordStartRealMs = nowMs();
    activeSegment = {
      index: route.segments.length,
      startFrame: route.frames.length,
      startT: round(recordBaseRouteMs, 3),
      startedAt: new Date().toISOString(),
      append: route.frames.length > 0,
    };
    route.segments.push(activeSegment);
    route.meta.config = flatConfig();
    route.meta.tasClock = tasClock();
    route.meta.macros = {
      speedBuildHoldMs: SPEEDBUILD_HOLD_MS,
      speedBuildPreCrouchMs: SPEEDBUILD_PRE_CROUCH_MS,
      speedBuildGroundSlideMs: SPEEDBUILD_GROUND_SLIDE_MS,
      autoBhopPreCrouchMs: AUTO_BHOP_PRE_CROUCH_MS,
      autoBhopGroundSlideMs: AUTO_BHOP_GROUND_SLIDE_MS,
    };
    route.updatedAt = new Date().toISOString();
    recording = true;
    lastStatus = activeSegment.append ? 'recording append' : 'recording';
    paint();
  }

  function stopRecording() {
    if (!recording) return;
    recording = false;
    stopSpeedBuild();
    macro.holdDown = false;
    if (activeSegment) {
      activeSegment.endFrame = Math.max(activeSegment.startFrame, route.frames.length - 1);
      activeSegment.endT = lastFrame() ? round(lastFrame().t, 3) : activeSegment.startT;
      activeSegment.frames = Math.max(0, activeSegment.endFrame - activeSegment.startFrame + 1);
      activeSegment.stoppedAt = new Date().toISOString();
    }
    activeSegment = null;
    route.updatedAt = new Date().toISOString();
    lastStatus = 'stopped';
    paint();
  }

  function toggleRecord() {
    if (recording) stopRecording();
    else startRecording();
  }

  function beginRecordHold() {
    if (!recording) startRecording();
    macro.holdDown = true;
    macro.holdStarted = nowMs();
    macro.speedBuild = false;
  }

  function endRecordHold() {
    macro.holdDown = false;
    stopSpeedBuild();
  }

  function appendFrame(pre, input, post, recon, moveLock, rawDt) {
    if (!recording || route.frames.length >= MAX_FRAMES) return;
    const t = recordBaseRouteMs + (nowMs() - recordStartRealMs);
    const prev = lastFrame();
    const simDt = tasInputDt(finite(input?.[1], prev ? finite(prev.simDt, TAS_DT_CAP_MS) : TAS_DT_CAP_MS));
    if (prev) recordSimMs += simDt;
    else recordSimMs = recordBaseSimMs;
    const frame = {
      n: route.frames.length,
      t: round(t, 3),
      dt: prev ? round(Math.max(0, t - finite(prev.t)), 3) : 0,
      simT: round(recordSimMs, 3),
      simDt: round(simDt, 3),
      rawSimDt: round(finite(rawDt, simDt), 3),
      recon: recon ? 1 : 0,
      moveLock: moveLock ? 1 : 0,
      input: cleanInput(input),
      pre,
      post,
    };
    if (!route.frames.length) route.start = pre;
    route.end = post;
    route.frames.push(frame);
  }

  function loadRouteFile(file) {
    if (!file) return;
    const reader = new FileReader();
    reader.onload = () => {
      try {
        route = normalizeLoadedRoute(JSON.parse(String(reader.result || '{}')));
        stopRecording();
        resetMacroRun();
        lastStatus = 'loaded ' + route.frames.length + ' frames';
        paint();
      } catch (e) {
        console.error('[TASRec] failed to load route json', e);
        lastStatus = 'load failed';
        paint();
      }
    };
    reader.readAsText(file);
  }

  function downloadRoute() {
    if (recording) stopRecording();
    route.updatedAt = new Date().toISOString();
    route.frameCount = route.frames.length;
    const text = JSON.stringify(route, null, 2);
    const blob = new Blob([text], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    const ts = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
    a.href = url;
    a.download = 'parkour-tas-route-' + ts + '.json';
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
    lastStatus = 'downloaded';
    paint();
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
      const rawDt = this.isYou && input ? finite(input[INPUT_INDEX.dt], TAS_DT_CAP_MS) : 0;
      if (this.isYou && input && recording) input[INPUT_INDEX.dt] = tasInputDt(input[INPUT_INDEX.dt]);
      if (this.isYou && input && recording) applyRecorderMacros(input, this);
      if (this.isYou && input) updateArcPreview(this, input);
      const shouldRecord = this.isYou && recording && input;
      const pre = shouldRecord ? snapPlayer(this) : null;
      const inputCopy = shouldRecord ? cleanInput(input) : null;
      const ret = original.call(this, input, game, recon, moveLock);
      if (shouldRecord) {
        try {
          appendFrame(pre, inputCopy, snapPlayer(this), recon, moveLock, rawDt);
        } catch (e) {
          console.warn('[TASRec] frame capture failed', e);
        }
      }
      return ret;
    };
    console.log('[TASRec] procInputs hooked');
  }

  function installPlayerHook() {
    const existing = Game?.players?.list?.find?.(p => p.isYou);
    if (existing) hookPlayer(existing);
    if (Game?.players?.add && !Game.players.__tasRecAddHook) {
      const origAdd = Game.players.add;
      Game.players.add = function (...args) {
        const p = origAdd.call(this, ...args);
        if (p?.isYou) hookPlayer(p);
        return p;
      };
      Game.players.__tasRecAddHook = true;
    }
  }

  function onGame(GUI, args) {
    const g = args && args[0];
    if (!g) return;
    Game = g;
    win._Game = g;
    waitForBody(() => {
      buildGUI();
      startArcVisualizer();
      installPlayerHook();
      lastStatus = 'ready';
      paint();
    });
  }

  function waitForBody(cb) {
    if (document.body) cb();
    else setTimeout(() => waitForBody(cb), 50);
  }

  function installGameCapture() {
    if (win._Game) {
      Game = win._Game;
      waitForBody(() => {
        buildGUI();
        startArcVisualizer();
        installPlayerHook();
        paint();
      });
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
    if (document.getElementById('tas-rec-gui')) return;
    const style = document.createElement('style');
    style.textContent = `
      #tas-rec-gui{position:fixed;left:18px;top:118px;z-index:2147483647;font:12px/1.35 Consolas,monospace;color:#cbd5e1;user-select:none}
      #tas-rec-panel{width:230px;background:rgba(5,8,12,.92);border:1px solid #2dd4bf;border-radius:7px;box-shadow:0 8px 28px rgba(0,0,0,.35);padding:10px}
      #tas-rec-title{font-weight:700;color:#5eead4;text-align:center;letter-spacing:.8px;margin-bottom:8px}
      #tas-rec-panel button,#tas-rec-panel label{display:block;box-sizing:border-box;width:100%;margin:5px 0;padding:6px 7px;border-radius:5px;border:1px solid #334155;background:rgba(15,23,42,.75);color:#e2e8f0;text-align:center;cursor:pointer;font:12px Consolas,monospace}
      #tas-rec-panel button:hover,#tas-rec-panel label:hover{background:rgba(30,41,59,.95)}
      #tas-rec-record.live{background:#7f1d1d;border-color:#ef4444;color:#fff}
      #tas-rec-download{border-color:#2563eb;color:#bfdbfe}
      #tas-rec-load-label{border-color:#0f766e;color:#99f6e4}
      #tas-rec-stats{margin-top:7px;color:#94a3b8;font-size:11px}
      #tas-rec-stats b{color:#fff}
      #tas-rec-hint{margin-top:5px;color:#64748b;font-size:10px}
    `;
    const box = document.createElement('div');
    box.id = 'tas-rec-gui';
    box.innerHTML = `
      <div id="tas-rec-panel">
        <div id="tas-rec-title">PARKOUR TAS RECORDER</div>
        <button id="tas-rec-record">RECORD / RESUME</button>
        <button id="tas-rec-stop">STOP</button>
        <label id="tas-rec-load-label">LOAD SEGMENT JSON<input id="tas-rec-load" type="file" accept="application/json,.json" style="display:none"></label>
        <button id="tas-rec-download">DOWNLOAD JSON</button>
        <div id="tas-rec-stats">
          <div>state: <b data-k="state">boot</b></div>
          <div>frames: <b data-k="frames">0</b></div>
          <div>segments: <b data-k="segments">0</b></div>
          <div>time: <b data-k="time">0.000</b>s</div>
          <div>R snap: <b data-k="snap">off</b></div>
          <div>clock: <b data-k="clock">20ms / q 33x1.1 / R 1x0.0033</b></div>
          <div>macro: <b data-k="macro">manual</b></div>
        </div>
        <div id="tas-rec-hint">Mouse4/Mouse5 hold = speedbuild. Middle click toggles auto-bhop. Hold R for TAS snap.</div>
      </div>`;
    document.documentElement.appendChild(style);
    document.documentElement.appendChild(box);

    guiEls = {
      record: box.querySelector('#tas-rec-record'),
      stop: box.querySelector('#tas-rec-stop'),
      load: box.querySelector('#tas-rec-load'),
      download: box.querySelector('#tas-rec-download'),
      state: box.querySelector('[data-k="state"]'),
      frames: box.querySelector('[data-k="frames"]'),
      segments: box.querySelector('[data-k="segments"]'),
      time: box.querySelector('[data-k="time"]'),
      snap: box.querySelector('[data-k="snap"]'),
      clock: box.querySelector('[data-k="clock"]'),
      macro: box.querySelector('[data-k="macro"]'),
    };
    guiEls.record.addEventListener('pointerdown', e => {
      e.preventDefault();
      beginRecordHold();
    });
    guiEls.record.addEventListener('pointerup', e => {
      e.preventDefault();
      endRecordHold();
    });
    guiEls.record.addEventListener('pointerleave', () => {
      if (macro.holdDown) endRecordHold();
    });
    guiEls.record.addEventListener('contextmenu', e => e.preventDefault());
    guiEls.stop.addEventListener('click', stopRecording);
    guiEls.download.addEventListener('click', downloadRoute);
    guiEls.load.addEventListener('change', e => loadRouteFile(e.target.files && e.target.files[0]));
    paint();
    setInterval(paint, 100);
  }

  function paint() {
    if (!guiEls) return;
    const last = lastFrame();
    guiEls.record.classList.toggle('live', recording);
    guiEls.record.textContent = recording ? 'RECORDING...' : 'RECORD / RESUME';
    guiEls.state.textContent = recording ? 'recording' : lastStatus;
    guiEls.frames.textContent = String(route.frames.length);
    guiEls.segments.textContent = String(route.segments.length);
    guiEls.time.textContent = ((last ? finite(last.t) : 0) / 1000).toFixed(3);
    guiEls.snap.textContent = win.__parkourTasSnap?.held ? 'on' : 'off';
    guiEls.clock.textContent = `${tasDtCapMs()}ms / q ${tasSnapSubframes()}x${tasSnapDtEach()} / R ${tasSlowSubframes()}x${tasSlowDtEach()}`;
    guiEls.macro.textContent = macro.speedBuild ? 'speedbuild' : macro.autoBhop ? 'auto-bhop' : macro.holdDown ? 'hold' : 'manual';
  }

  function installMouseButtons() {
    window.addEventListener('mousedown', e => {
      if (e.button === 3 || e.button === 4) {
        e.preventDefault();
        e.stopPropagation();
        beginRecordHold();
      } else if (e.button === 1) {
        e.preventDefault();
        e.stopPropagation();
        toggleAutoBhop();
      }
    }, true);
    window.addEventListener('mouseup', e => {
      if (e.button === 3 || e.button === 4) {
        e.preventDefault();
        e.stopPropagation();
        endRecordHold();
      }
    }, true);
    window.addEventListener('auxclick', e => {
      if (e.button === 1 || e.button === 3 || e.button === 4) {
        e.preventDefault();
        e.stopPropagation();
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

  // Keep the game "focused + visible" so it doesn't pause/throttle input when
  // this tab isn't the active window — this is what forced manual focus while
  // recording. Runs in page context so it overrides what the game itself reads.
  // NOTE: this defeats the GAME's blur-pause; browsers still throttle rAF for a
  // fully backgrounded/minimized tab, so record with the window merely unfocused
  // (e.g. side-by-side), not minimized.
  function installFocusSpoof() {
    if (win.__parkourTasFocusSpoofInstalled) return;
    win.__parkourTasFocusSpoofInstalled = true;
    const src = `(()=>{if(window.__parkourTasFocusSpoof)return;window.__parkourTasFocusSpoof=1;` +
      `try{Object.defineProperty(document,'hidden',{configurable:true,get:()=>false});}catch(e){}` +
      `try{Object.defineProperty(document,'visibilityState',{configurable:true,get:()=>'visible'});}catch(e){}` +
      `try{Object.defineProperty(document,'webkitHidden',{configurable:true,get:()=>false});}catch(e){}` +
      `try{Object.defineProperty(document,'webkitVisibilityState',{configurable:true,get:()=>'visible'});}catch(e){}` +
      `document.hasFocus=()=>true;` +
      `const sw=e=>{try{e.stopImmediatePropagation();}catch(_){}};` +
      `window.addEventListener('blur',sw,true);document.addEventListener('visibilitychange',sw,true);` +
      `document.addEventListener('webkitvisibilitychange',sw,true);window.addEventListener('focus',sw,true);` +
      `})();`;
    const s = document.createElement('script');
    s.textContent = src;
    (document.head || document.documentElement).appendChild(s);
    s.remove();
  }

  win.__parkourTasRecorder = {
    get route() { return route; },
    get recording() { return recording; },
    start: startRecording,
    stop: stopRecording,
    download: downloadRoute,
    loadObject(obj) { route = normalizeLoadedRoute(obj); paint(); },
  };

  installFocusSpoof();
  installRSnap();
  installMouseButtons();
  installGameCapture();
})();
