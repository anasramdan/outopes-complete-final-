/* أتوبيس كمبليت — السيرفر (بدون أي مكتبات خارجية)
   الملفات الأربعة يجب أن تكون في نفس المجلد: server.js و index.html و words.js و package.json
   التشغيل:  node server.js   أو   npm start */
const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const CATS = ['boy', 'girl', 'thing', 'animal', 'plant', 'country'];
const LETTERS = 'أبتثجحخدذرزسشصضطظعغفقكلمنهوي'.split('');   // 28 حرفاً = 28 جولة كحد أقصى
const MAX_ROUNDS = 28;
const UNIQUE_POINTS = 10;   // إجابة غير مكررة (6 × 10 = 60)
const DUP_POINTS = 5;       // إجابة مكررة
const MAX_PLAYERS = 12;

const rooms = {};    // code -> room
const players = {};  // pid -> {pid, code, res, drop}

/* ---------- أدوات ---------- */
function normText(s) {
  return String(s || '').trim()
    .replace(/[\u064B-\u065F\u0670\u0640]/g, '')            // التشكيل والتطويل
    .replace(/[أإآٱ]/g, 'ا').replace(/ى/g, 'ي').replace(/ة/g, 'ه')
    .replace(/ؤ/g, 'و').replace(/ئ/g, 'ي')
    .replace(/ک/g, 'ك').replace(/[یې]/g, 'ي').replace(/ھ/g, 'ه')
    .replace(/\s+/g, ' ');
}

/* تحليل الكلمة: الشكل الكامل، وهل تبدأ بـ "ال" التعريف، والشكل بعد حذفها.
   ملاحظة: "ألمانيا" (بهمزة) كلمة تبدأ بـ أ، أما "الأسد" (ال بدون همزة) فهي "ال" التعريف. */
function formsOf(raw) {
  const o = String(raw || '')
    .replace(/[\u064B-\u065F\u0670\u0640]/g, '')                       // التشكيل والتطويل
    .replace(/[.,،؛;:!?؟"'`()\[\]{}\-_*\/\\«»]/g, ' ')                  // علامات الترقيم
    .trim().replace(/\s+/g, '');
  const full = normText(o);
  const bare = o.startsWith('ال') && full.length > 3;
  return { full, bare, stripped: bare ? full.slice(2) : full };
}

/* قاموس الكلمات الصحيحة (words.js) */
const WORDS = require('./words.js');
const DMAP = {};
Object.keys(WORDS).forEach(c => {
  const m = new Map();
  WORDS[c].split(/\s+/).filter(Boolean).forEach(w => {
    const f = formsOf(w.replace(/_/g, ' '));
    const canon = f.bare ? f.stripped : f.full;
    m.set(f.full, canon); m.set(f.stripped, canon);
  });
  DMAP[c] = m;
});
const lookup = (cat, f) => DMAP[cat].get(f.full) || DMAP[cat].get(f.stripped) || null;
const CAT_NAMES = { boy: 'اسم ولد', girl: 'اسم بنت', thing: 'جماد', animal: 'حيوان', plant: 'نبات', country: 'بلاد' };
const VOTE_MS = 30000;   // مهلة مراجعة الكلمات غير المعروفة
const isNameCat = c => c === 'boy' || c === 'girl';

/* تصنيف إجابة واحدة: known / unknown (تحتاج تصويت) / bad / empty — مع سبب واضح لأي رفض */
function classify(cat, raw, L, letterShown) {
  raw = String(raw || '').trim().slice(0, 30);
  const f = formsOf(raw);
  if (!f.full) return { raw, key: '', st: 'empty', note: '' };
  const hit = lookup(cat, f);
  const startsOk = (hit && hit.startsWith(L)) || f.stripped.startsWith(L);
  if (!startsOk) {
    const note = f.bare
      ? `لا تبدأ بحرف ${letterShown} (بعد "ال" تبدأ بحرف ${f.stripped.charAt(0)})`
      : `لا تبدأ بحرف ${letterShown}`;
    return { raw, key: f.stripped, st: 'bad', note };
  }
  if (hit) return { raw, key: hit, st: 'known', note: '' };
  if (f.stripped.length < 2 || /^(.)\1*$/.test(f.stripped) || /[0-9٠-٩A-Za-z]/.test(f.full))
    return { raw, key: f.stripped, st: 'bad', note: 'كلمة غير مفهومة' };
  const elsewhere = Object.keys(DMAP).filter(c => c !== cat && lookup(c, f));
  // أسماء الأولاد والبنات تتداخل كثيراً (نور، جود…) فلا نرفضها تلقائياً: تذهب لتصويت اللاعبين
  const sameKind = isNameCat(cat) ? [] : elsewhere.filter(c => !isNameCat(c));
  if (sameKind.length)
    return { raw, key: f.stripped, st: 'bad', note: 'هذه الكلمة من خانة ' + CAT_NAMES[sameKind[0]] + ' وليست من نوع هذه الخانة' };
  return { raw, key: f.stripped, st: 'unknown', note: '' };
}

/* ---------- أدوات ---------- */
function genCode() {
  const ch = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
  let s;
  do { s = ''; for (let i = 0; i < 5; i++) s += ch[Math.floor(Math.random() * ch.length)]; } while (rooms[s]);
  return s;
}
function lanAddrs() {
  const out = [];
  const ifs = os.networkInterfaces();
  Object.keys(ifs).forEach(n => (ifs[n] || []).forEach(i => {
    if (i.family === 'IPv4' && !i.internal) out.push('http://' + i.address + ':' + PORT);
  }));
  return out;
}

/* ---------- حالة الغرفة ---------- */
function pub(room) {
  return {
    code: room.code, phase: room.phase, round: room.round, totalRounds: room.totalRounds,
    duration: room.duration, letter: room.letter, results: room.results,
    vote: (room.phase === 'voting' && room.vote) ? {
      items: room.vote.items.map(i => ({ id: i.id, cat: i.cat, word: i.word, authors: i.authors })),
      ms: Math.max(0, room.vote.end - Date.now())
    } : null,
    players: room.players.map(p => ({ id: p.id, name: p.name, score: p.score, eliminated: p.eliminated, left: p.left, host: p.host }))
  };
}
function send(pid, data) {
  const pl = players[pid];
  if (pl && pl.res) { try { pl.res.write('data: ' + JSON.stringify(data) + '\n\n'); } catch (e) {} }
}
function broadcast(room) {
  const m = pub(room);
  room.players.forEach(p => { if (!p.left) send(p.id, m); });
}
const active = room => room.players.filter(p => !p.eliminated && !p.left);

/* ---------- منطق اللعبة ---------- */
function startRound(room) {
  room.round++;
  let pool = LETTERS.filter(l => !room.used.includes(l));
  if (!pool.length) { room.used = []; pool = LETTERS.slice(); }
  room.letter = pool[Math.floor(Math.random() * pool.length)];
  room.used.push(room.letter);
  room.results = null; room.answers = {}; room.drafts = {};
  room.phase = 'playing';
  broadcast(room);
  clearTimeout(room.roundTimer);
  room.roundTimer = setTimeout(() => startCollect(room), room.duration * 1000 + 800);
}
function startCollect(room) {
  if (room.phase !== 'playing') return;
  clearTimeout(room.roundTimer);
  room.phase = 'collecting'; room.answers = {};
  broadcast(room);
  clearTimeout(room.collectTimer);
  room.collectTimer = setTimeout(() => finishRound(room), 6000);
  checkCollected(room);
}
function checkCollected(room) {
  if (room.phase !== 'collecting') return;
  if (active(room).every(p => room.answers[p.id])) finishRound(room);
}
function finishRound(room) {
  if (room.phase !== 'collecting') return;
  clearTimeout(room.collectTimer);
  const L = normText(room.letter);
  room.cls = {};
  const itemMap = {};
  room.players.forEach(p => {
    if (p.left || p.eliminated) return;
    room.cls[p.id] = {};
    const ans = room.answers[p.id] || room.drafts[p.id] || {};
    CATS.forEach(c => {
      const r = classify(c, ans[c], L, room.letter);
      room.cls[p.id][c] = r;
      if (r.st === 'unknown') {
        const k = c + '|' + r.key;
        if (!itemMap[k]) itemMap[k] = { cat: c, key: r.key, word: r.raw, authors: [] };
        itemMap[k].authors.push(p.id);
      }
    });
  });
  const items = Object.values(itemMap).map((it, i) => Object.assign(it, { id: i }));
  if (!items.length) { finalizeRound(room, {}); return; }
  room.vote = { items, votes: {}, end: Date.now() + VOTE_MS };
  room.phase = 'voting';
  broadcast(room);
  clearTimeout(room.voteTimer);
  room.voteTimer = setTimeout(() => endVoting(room), VOTE_MS);
  checkVoted(room);
}
function voters(room) {
  return active(room).filter(p => room.vote.items.some(it => !it.authors.includes(p.id)));
}
function checkVoted(room) {
  if (room.phase !== 'voting' || !room.vote) return;
  if (voters(room).every(p => room.vote.votes[p.id])) endVoting(room);
}
function endVoting(room) {
  if (room.phase !== 'voting' || !room.vote) return;
  clearTimeout(room.voteTimer);
  const verdict = {};
  room.vote.items.forEach(it => {
    let yes = 0, no = 0;
    active(room).forEach(p => {
      if (it.authors.includes(p.id)) return;
      const v = room.vote.votes[p.id];
      if (!v) return;
      if (v[it.id] === false) no++; else yes++;
    });
    verdict[it.cat + '|' + it.key] = (yes >= no) ? 'yes' : 'no';
  });
  finalizeRound(room, verdict);
}
function finalizeRound(room, verdict) {
  const counts = {};
  CATS.forEach(c => { counts[c] = {}; });
  const fin = {};
  Object.keys(room.cls).forEach(pid => {
    const pl = room.players.find(x => x.id === pid);
    if (!pl || pl.left) return;
    fin[pid] = {};
    CATS.forEach(c => {
      const r = room.cls[pid][c];
      let valid = false, note = r.note;
      if (r.st === 'known') valid = true;
      else if (r.st === 'unknown') {
        const v = verdict[c + '|' + r.key];
        if (v === 'no') note = 'رفضها اللاعبون';
        else { valid = true; note = v === 'yes' ? 'قبلها اللاعبون' : ''; }
      }
      fin[pid][c] = { raw: r.raw, key: r.key, st: r.st, valid, note };
      if (valid) counts[c][r.key] = (counts[c][r.key] || 0) + 1;
    });
  });
  const rows = [];
  room.players.forEach(p => {
    if (p.left) return;
    const cells = {}; let total = 0;
    CATS.forEach(c => {
      if (p.eliminated || !fin[p.id]) { cells[c] = { a: '', pts: 0, s: 'x', n: '' }; return; }
      const f = fin[p.id][c];
      let pts = 0, s;
      if (f.valid) {
        if (counts[c][f.key] > 1) { pts = DUP_POINTS; s = 'dup'; } else { pts = UNIQUE_POINTS; s = 'ok'; }
      } else s = f.st === 'empty' ? 'empty' : 'bad';
      cells[c] = { a: f.raw, pts, s, n: f.note }; total += pts;
    });
    p.score += total;
    rows.push({ id: p.id, name: p.name, cells, total, eliminated: p.eliminated });
  });
  room.results = { letter: room.letter, rows };
  room.vote = null;
  room.phase = 'results';
  broadcast(room);
}

function addPlayer(room, name, host) {
  name = String(name || '').trim().slice(0, 16) || 'لاعب';
  const base = name; let n = 2;
  while (room.players.some(p => p.name === name && !p.left)) name = base + ' ' + (n++);
  const pid = crypto.randomBytes(8).toString('hex');
  room.players.push({ id: pid, name, score: 0, eliminated: false, left: false, host });
  players[pid] = { pid, code: room.code, res: null, drop: null };
  return pid;
}
function leave(pid) {
  const pl = players[pid];
  if (!pl) return;
  delete players[pid];
  clearTimeout(pl.drop);
  const old = pl.res; pl.res = null;
  if (old) { try { old.end(); } catch (e) {} }
  const room = rooms[pl.code];
  if (!room) return;
  const i = room.players.findIndex(p => p.id === pid);
  if (i < 0) return;
  const p = room.players[i];
  if (room.phase === 'lobby') room.players.splice(i, 1); else p.left = true;
  if (p.host) {
    p.host = false;
    const nh = room.players.find(x => !x.left);
    if (nh) nh.host = true;
  }
  if (!room.players.some(x => !x.left)) {
    clearTimeout(room.roundTimer); clearTimeout(room.collectTimer); clearTimeout(room.voteTimer);
    delete rooms[room.code];
    return;
  }
  broadcast(room);
  if (room.phase === 'playing' && !active(room).length) startCollect(room);
  else { checkCollected(room); checkVoted(room); }
}

function handleAct(body) {
  const pl = players[body.pid];
  if (!pl) return { error: 'الجلسة منتهية' };
  const room = rooms[pl.code];
  if (!room) return { error: 'الغرفة غير موجودة' };
  const p = room.players.find(x => x.id === body.pid);
  if (!p) return { error: 'لاعب غير معروف' };

  switch (body.type) {
    case 'start':
      if (p.host && room.phase === 'lobby') {
        room.totalRounds = Math.min(MAX_ROUNDS, Math.max(1, parseInt(body.rounds, 10) || 5));
        room.duration = Math.min(300, Math.max(20, parseInt(body.duration, 10) || 90));
        startRound(room);
      }
      break;
    case 'done':
      if (room.phase === 'playing' && !p.eliminated) startCollect(room);
      break;
    case 'draft':
      if ((room.phase === 'playing' || room.phase === 'collecting') && !p.eliminated) {
        const a = {};
        CATS.forEach(c => { a[c] = String((body.a || {})[c] || '').slice(0, 40); });
        room.drafts[p.id] = a;
      }
      break;
    case 'answers':
      if (room.phase === 'collecting' && !p.eliminated) {
        const a = {};
        CATS.forEach(c => { a[c] = String((body.a || {})[c] || '').slice(0, 40); });
        room.answers[p.id] = a;
        checkCollected(room);
      }
      break;
    case 'vote':
      if (room.phase === 'voting' && room.vote && !p.eliminated) {
        const v = {};
        room.vote.items.forEach(it => { if (!it.authors.includes(p.id)) v[it.id] = !(body.v && body.v[it.id] === false); });
        room.vote.votes[p.id] = v;
        checkVoted(room);
      }
      break;
    case 'cheat':
      if (room.phase === 'playing' && !p.eliminated) {
        p.eliminated = true;
        broadcast(room);
        if (!active(room).length) startCollect(room);
      }
      break;
    case 'next':
      if (p.host && room.phase === 'results') {
        if (room.round >= room.totalRounds) { room.phase = 'final'; broadcast(room); }
        else startRound(room);
      }
      break;
    case 'again':
      if (p.host && room.phase === 'final') {
        room.round = 0; room.used = []; room.results = null; room.letter = '';
        room.players.forEach(x => { x.score = 0; x.eliminated = false; });
        room.phase = 'lobby';
        broadcast(room);
      }
      break;
    case 'leave':
      leave(body.pid);
      break;
  }
  return { ok: true };
}

/* ---------- HTTP ---------- */
function readBody(req, cb) {
  let d = '';
  req.on('data', c => { d += c; if (d.length > 1e5) req.destroy(); });
  req.on('end', () => { try { cb(JSON.parse(d || '{}')); } catch (e) { cb(null); } });
}
function json(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8' });
  res.end(JSON.stringify(obj));
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');

  if (req.method === 'GET' && (url.pathname === '/' || url.pathname === '/index.html')) {
    fs.readFile(path.join(__dirname, 'index.html'), (err, data) => {
      if (err) { res.writeHead(500); return res.end('index.html غير موجود بجانب server.js'); }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' });
      res.end(data);
    });
    return;
  }

  if (req.method === 'GET' && url.pathname === '/healthz') { res.writeHead(200); res.end('ok'); return; }

  if (req.method === 'GET' && url.pathname === '/api/events') {
    const pid = url.searchParams.get('pid');
    const pl = players[pid];
    if (!pl || !rooms[pl.code]) { res.writeHead(404); return res.end(); }
    res.writeHead(200, {
      'Content-Type': 'text/event-stream; charset=utf-8',
      'Cache-Control': 'no-cache, no-transform',
      'Connection': 'keep-alive',
      'X-Accel-Buffering': 'no'
    });
    res.write('retry: 2000\n\n');
    if (pl.res) { const o = pl.res; pl.res = null; try { o.end(); } catch (e) {} }
    pl.res = res;
    clearTimeout(pl.drop); pl.drop = null;
    send(pid, pub(rooms[pl.code]));
    const hb = setInterval(() => { try { res.write(': ping\n\n'); } catch (e) {} }, 20000);
    res.on('close', () => {
      clearInterval(hb);
      if (pl.res === res) {
        pl.res = null;
        pl.drop = setTimeout(() => leave(pid), 8000);   // مهلة لإعادة الاتصال
      }
    });
    return;
  }

  if (req.method === 'POST' && url.pathname.startsWith('/api/')) {
    readBody(req, body => {
      if (!body) return json(res, 400, { error: 'طلب غير صالح' });

      if (url.pathname === '/api/create') {
        const code = genCode();
        const room = {
          code, phase: 'lobby', round: 0, totalRounds: 5, duration: 90, letter: '', results: null,
          used: [], players: [], answers: {}, drafts: {}, cls: null, vote: null, roundTimer: null, collectTimer: null, voteTimer: null
        };
        rooms[code] = room;
        const pid = addPlayer(room, body.name, true);
        return json(res, 200, { pid, code, addrs: lanAddrs() });
      }
      if (url.pathname === '/api/join') {
        const code = String(body.code || '').trim().toUpperCase();
        const room = rooms[code];
        if (!room) return json(res, 200, { error: 'لا توجد غرفة بهذا الكود.' });
        if (room.phase !== 'lobby') return json(res, 200, { error: 'اللعبة بدأت بالفعل، انتظر الجولة القادمة.' });
        if (room.players.filter(p => !p.left).length >= MAX_PLAYERS) return json(res, 200, { error: 'الغرفة ممتلئة.' });
        const pid = addPlayer(room, body.name, false);
        broadcast(room);
        return json(res, 200, { pid, code, addrs: lanAddrs() });
      }
      if (url.pathname === '/api/act') return json(res, 200, handleAct(body));
      json(res, 404, { error: 'غير موجود' });
    });
    return;
  }

  res.writeHead(404); res.end('Not found');
});

if (require.main === module) server.listen(PORT, '0.0.0.0', () => {
  console.log('\n🚌 أتوبيس كمبليت يعمل الآن!\n');
  console.log('على نفس الجهاز:   http://localhost:' + PORT);
  const a = lanAddrs();
  if (a.length) { console.log('للاعبين الآخرين (نفس الشبكة / الواي فاي):'); a.forEach(x => console.log('   ' + x)); }
  else console.log('لم يتم العثور على عنوان IP للشبكة. تأكد من اتصالك بالواي فاي.');
  console.log('\nلإيقاف السيرفر اضغط Ctrl + C\n');
});

module.exports = { classify, normText, formsOf };
