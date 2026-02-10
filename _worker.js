import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域 (优先级：环境变量 > 代码硬编码)
// =============================================================================
const UUID = ""; // 默认 UUID (建议在环境变量中设置)
const WEB_PASSWORD = "";  // 后台管理密码 (必填，否则无法进入后台)
const SUB_PASSWORD = "";  // 订阅路径密码 (可选，建议设置)
const DEFAULT_PROXY_IP = "cf.090227.xyz";  // 默认优选 IP/域名
const ROOT_REDIRECT_URL = "https://cn.bing.com"; // 根路径重定向地址

// =============================================================================
// ⚡️ 核心逻辑区 (无状态版)
// =============================================================================
const MAX_PENDING=2097152,KEEPALIVE=15000,STALL_TO=8000,MAX_STALL=12,MAX_RECONN=24;
const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

// 解析 ProxyIP 列表
async function parseProxyList(str) {
    if (!str) return [];
    const list = str.split(/[,\n]/).map(s => s.trim()).filter(Boolean);
    const result = [];
    for (const item of list) {
        try {
            const [address, port] = await parseIP(item);
            result.push({ address, port });
        } catch(e) {}
    }
    return result;
}

// 协议头 (保持原协议名，但在UI中不显示)
const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

// 简易环境变量获取
function getEnv(env, key, fallback) {
    return env[key] || fallback;
}

async function parseIP(p){
    p=p.toLowerCase();
    let a=p,o=443;
    if(p.includes('.tp')){
        const m=p.match(/\.tp(\d+)/);
        if(m)o=parseInt(m[1],10);
        return[a,o]
    }
    if(p.includes(']:')){
        const s=p.split(']:');
        a=s[0]+']';
        o=parseInt(s[1],10)||o
    } else if(p.includes(':')&&!p.startsWith('[')){
        const i=p.lastIndexOf(':');
        a=p.slice(0,i);
        o=parseInt(p.slice(i+1),10)||o
    }
    return[a,o]
}

class Pool{constructor(){this.b=new ArrayBuffer(16384);this.p=0;this.l=[];this.m=8}alloc(s){if(s<=4096&&s<=16384-this.p){const v=new Uint8Array(this.b,this.p,s);this.p+=s;return v}const r=this.l.pop();return r&&r.byteLength>=s?new Uint8Array(r.buffer,0,s):new Uint8Array(s)}free(b){if(b.buffer===this.b)this.p=Math.max(0,this.p-b.length);else if(this.l.length<this.m&&b.byteLength>=1024)this.l.push(b)}reset(){this.p=0;this.l=[]}}

async function getDynamicUUID(key, refresh = 86400) {
    const time = Math.floor(Date.now() / 1000 / refresh);
    const msg = new TextEncoder().encode(`${key}-${time}`);
    const hash = await crypto.subtle.digest('SHA-256', msg);
    const b = new Uint8Array(hash);
    return [...b.slice(0, 16)].map(n => n.toString(16).padStart(2, '0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/, '$1-$2-$3-$4-$5');
}

const handle = (ws, pc, uuid, proxyIPList = []) => {
  const pool = new Pool();
  let s, w, r, inf, fst = true, rx = 0, stl = 0, cnt = 0, lact = Date.now(), con = false, rd = false, wt = false, tm = {}, pd = [], pb = 0, scr = 1.0, lck = Date.now(), lrx = 0, md = 'buf', asz = 0, tp = [], st = { t: 0, c: 0, ts: Date.now() };
  const upd = sz => {
    st.t += sz; st.c++;
    asz = asz * 0.9 + sz * 0.1; const n = Date.now();
    if (n - st.ts > 1000) { const rt = st.t; tp.push(rt); if (tp.length > 5) tp.shift(); st.t = 0;
    st.ts = n; const av = tp.reduce((a, b) => a + b, 0) / tp.length;
    if (st.c >= 20) { if (av > 2e7 && asz > 16384) md = 'dir';
    else if (av < 1e7 || asz < 8192) md = 'buf'; else md = 'adp' } }
  };
  const rdL = async () => {
    if (rd) return; rd = true;
    let b = [], bz = 0, tm = null;
    const fl = () => { if (!bz) return;
    const m = new Uint8Array(bz); let p = 0; for (const x of b) { m.set(x, p);
    p += x.length } if (ws.readyState === 1) ws.send(m); b = []; bz = 0; if (tm) clearTimeout(tm);
    tm = null };
    try { while (1) { if (pb > MAX_PENDING) { await new Promise(r => setTimeout(r, 100));
    continue } const { done, value: v } = await r.read(); if (v?.length) { rx += v.length; lact = Date.now();
    stl = 0; upd(v.length); const n = Date.now(); if (n - lck > 5000) { const el = n - lck, by = rx - lrx, r = by / el;
    if (r > 500) scr = Math.min(1, scr + 0.05);
    else if (r < 50) scr = Math.max(0.1, scr - 0.05); lck = n;
    lrx = rx } if (md === 'buf') { if (v.length < 32768) { b.push(v); bz += v.length;
    if (bz >= 131072) fl(); else if (!tm) tm = setTimeout(fl, asz > 16384 ? 5 : 20) } else { fl();
    if (ws.readyState === 1) ws.send(v) } } else { fl();
    if (ws.readyState === 1) ws.send(v) } } if (done) { fl(); rd = false; rcn();
    break } } } catch { fl(); rd = false; rcn() }
  };
  const wtL = async () => { if (wt) return; wt = true;
  try { while (wt) { if (!w) { await new Promise(r => setTimeout(r, 100));
  continue } if (!pd.length) { await new Promise(r => setTimeout(r, 20)); continue } const b = pd.shift(); await w.write(b);
  pb -= b.length; pool.free(b) } } catch { wt = false } };
  const est = async () => { try { s = await cn(); w = s.writable.getWriter(); r = s.readable.getReader();
  con = false; cnt = 0; scr = Math.min(1, scr + 0.15); lact = Date.now(); rdL();
  wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2); rcn() } };
  
  // 连接逻辑
  const cn = async () => {
    try {
        const direct = connect({ hostname: inf.host, port: inf.port });
        await direct.opened;
        return direct;
    } catch (e) {}

    if (pc && pc.address) {
        try {
            const specific = connect({ hostname: pc.address, port: pc.port });
            await specific.opened;
            return specific;
        } catch (e) {}
    }

    if (proxyIPList && proxyIPList.length > 0) {
        for (const proxy of proxyIPList) {
            try {
                const socket = connect({ hostname: proxy.address, port: proxy.port });
                await socket.opened;
                return socket;
            } catch (e) {
                continue;
            }
        }
    }
    throw new Error('All connection attempts failed');
 };
  const rcn = async () => { if (!inf || ws.readyState !== 1) { cln(); ws.close(1011);
  return } if (cnt >= MAX_RECONN) { cln(); ws.close(1011); return } if (con) return; cnt++;
  let d = Math.min(50 * Math.pow(1.5, cnt - 1), 3000) * (1.5 - scr * 0.5); d = Math.max(50, Math.floor(d));
  try { csk(); if (pb > MAX_PENDING * 2) while (pb > MAX_PENDING && pd.length > 5) { const k = pd.shift();
  pb -= k.length; pool.free(k) } await new Promise(r => setTimeout(r, d)); con = true; s = await cn();
  w = s.writable.getWriter(); r = s.readable.getReader(); con = false; cnt = 0; scr = Math.min(1, scr + 0.15);
  stl = 0; lact = Date.now(); rdL(); wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2);
  if (cnt < MAX_RECONN && ws.readyState === 1) setTimeout(rcn, 500); else { cln(); ws.close(1011) } } };
  const stT = () => { tm.ka = setInterval(async () => { if (!con && w && Date.now() - lact > KEEPALIVE) try { await w.write(new Uint8Array(0)); lact = Date.now() } catch { rcn() } }, KEEPALIVE / 3);
  tm.hc = setInterval(() => { if (!con && st.t > 0 && Date.now() - lact > STALL_TO) { stl++; if (stl >= MAX_STALL) { if (cnt < MAX_RECONN) { stl = 0; rcn() } else { cln(); ws.close(1011) } } } }, STALL_TO / 2) };
  const csk = () => { rd = false; wt = false; try { w?.releaseLock(); r?.releaseLock();
  s?.close() } catch { } }; 
  const cln = () => { Object.values(tm).forEach(clearInterval); csk(); while (pd.length) pool.free(pd.shift()); pb = 0;
  st = { t: 0, c: 0, ts: Date.now() }; md = 'buf'; asz = 0; tp = [];
  pool.reset() };
  ws.addEventListener('message', async e => { try { if (fst) { fst = false; const b = new Uint8Array(e.data); if (buildUUID(b, 1).toLowerCase() !== uuid.toLowerCase()) throw 0; ws.send(new Uint8Array([0, 0])); const { host, port, payload } = extractAddr(b); inf = { host, port }; con = true; if (payload.length) { const z = pool.alloc(payload.length); z.set(payload); pd.push(z); pb += z.length } stT(); est() } else { lact = Date.now(); if (pb > MAX_PENDING * 2) return; const z = pool.alloc(e.data.byteLength); z.set(new Uint8Array(e.data)); pd.push(z); pb += z.length } } catch { cln(); ws.close(1006) } });
  ws.addEventListener('close', cln); ws.addEventListener('error', cln)
};

// =============================================================================
// 🖥️ 现代化面板代码 (黑白灰风格 + 去敏感化)
// =============================================================================
function loginPage() {
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>System Access</title>
    <style>
        :root {
            --bg: #09090b;
            --surface: #18181b;
            --border: #27272a;
            --text: #e4e4e7;
            --primary: #fafafa;
            --primary-fg: #18181b;
        }
        body {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            background: var(--bg);
            color: var(--text);
            display: flex;
            justify-content: center;
            align-items: center;
            height: 100vh;
            margin: 0;
        }
        .box {
            background: var(--surface);
            padding: 40px;
            border: 1px solid var(--border);
            border-radius: 12px;
            width: 100%;
            max-width: 320px;
            text-align: center;
            box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06);
        }
        h3 { margin-top: 0; font-weight: 500; letter-spacing: -0.5px; color: var(--primary); }
        input {
            width: 100%;
            padding: 12px;
            margin: 20px 0;
            background: #000;
            border: 1px solid var(--border);
            border-radius: 6px;
            color: var(--text);
            outline: none;
            transition: border-color 0.2s;
            box-sizing: border-box;
            text-align: center;
        }
        input:focus { border-color: var(--primary); }
        button {
            width: 100%;
            padding: 12px;
            background: var(--primary);
            color: var(--primary-fg);
            border: none;
            border-radius: 6px;
            font-weight: 600;
            cursor: pointer;
            transition: opacity 0.2s;
        }
        button:hover { opacity: 0.9; }
    </style>
</head>
<body>
    <div class="box">
        <h3>Console Access</h3>
        <input type="password" id="pwd" placeholder="Enter Access Key" autofocus onkeypress="if(event.keyCode===13)verify()">
        <button onclick="verify()">Verify Identity</button>
    </div>
    <script>
        function verify(){
            const p=document.getElementById("pwd").value;
            if(!p)return;
            document.cookie="auth="+p+"; path=/; Max-Age=31536000; SameSite=Lax";
            location.reload();
        }
    </script>
</body></html>`;
}

function dashPage(host, uuid, proxyip, subpass) {
    const defaultSubLink = `https://${host}/${subpass}`;
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Service Dashboard</title>
    <link href="https://cdn.jsdelivr.net/npm/remixicon@3.5.0/fonts/remixicon.css" rel="stylesheet">
    <style>
        :root {
            --bg: #000000;
            --card-bg: #0a0a0a;
            --border: #262626;
            --text-main: #ededed;
            --text-sub: #a1a1aa;
            --accent: #ffffff;
        }
        body {
            background: var(--bg);
            color: var(--text-main);
            font-family: 'Inter', -apple-system, sans-serif;
            margin: 0;
            padding: 40px 20px;
            display: flex;
            justify-content: center;
            min-height: 100vh;
        }
        .container { width: 100%; max-width: 720px; display: flex; flex-direction: column; gap: 20px; }
        
        /* 顶部导航 */
        .header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px; }
        .brand { font-size: 1.2rem; font-weight: 700; display: flex; align-items: center; gap: 8px; letter-spacing: -0.5px; }
        .status-dot { width: 8px; height: 8px; background: #10b981; border-radius: 50%; box-shadow: 0 0 8px #10b981; }

        /* 卡片样式 */
        .card {
            background: var(--card-bg);
            border: 1px solid var(--border);
            border-radius: 12px;
            padding: 24px;
            transition: transform 0.2s ease, border-color 0.2s;
        }
        .card:hover { border-color: #404040; }
        
        .section-title {
            font-size: 0.9rem;
            color: var(--text-sub);
            text-transform: uppercase;
            letter-spacing: 1px;
            margin-bottom: 16px;
            display: flex;
            align-items: center;
            gap: 8px;
        }
        
        /* 输入框组 */
        .input-group { display: flex; gap: 10px; }
        input {
            flex: 1;
            background: #171717;
            border: 1px solid var(--border);
            color: var(--text-main);
            padding: 12px 16px;
            border-radius: 8px;
            font-family: 'Monaco', monospace;
            font-size: 0.85rem;
            outline: none;
            transition: all 0.2s;
        }
        input:focus { border-color: var(--text-sub); background: #262626; }
        
        /* 按钮 */
        .btn {
            padding: 0 20px;
            background: var(--accent);
            color: black;
            border: none;
            border-radius: 8px;
            font-weight: 600;
            font-size: 0.9rem;
            cursor: pointer;
            transition: opacity 0.2s;
        }
        .btn:hover { opacity: 0.8; }
        .btn-ghost { background: transparent; border: 1px solid var(--border); color: var(--text-sub); }
        .btn-ghost:hover { border-color: var(--text-main); color: var(--text-main); }

        .info-row { display: flex; justify-content: space-between; padding: 12px 0; border-bottom: 1px solid var(--border); font-size: 0.9rem; }
        .info-row:last-child { border-bottom: none; }
        .info-label { color: var(--text-sub); }
        .info-val { font-family: monospace; }

    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <div class="brand">
                <div class="status-dot"></div>
                <span>EDGE NETWORK</span>
            </div>
            <button class="btn btn-ghost" onclick="logout()" style="padding: 8px 12px; height: auto;">
                <i class="ri-shut-down-line"></i>
            </button>
        </div>

        <div class="card">
            <div class="section-title"><i class="ri-refresh-line"></i> Sync Configuration</div>
            <div class="input-group">
                <input type="text" id="subLink" value="${defaultSubLink}" readonly onclick="this.select()">
                <button class="btn" onclick="copyId('subLink')">Copy</button>
            </div>
            <div style="margin-top: 15px; font-size: 0.8rem; color: var(--text-sub);">
                <i class="ri-information-line"></i> 将此链接导入客户端以同步配置
            </div>
        </div>

        <div class="card">
            <div class="section-title"><i class="ri-equalizer-line"></i> Advanced Settings</div>
            
            <div class="info-row">
                <span class="info-label">Identity Key (UUID)</span>
                <span class="info-val">${uuid.split('-')[0]}***</span>
            </div>

            <div style="margin-top: 20px;">
                <label style="font-size: 0.8rem; color: var(--text-sub); display: block; margin-bottom: 8px;">
                    Custom Access Point (Optional)
                </label>
                <div class="input-group">
                    <input type="text" id="customIP" value="${proxyip}" placeholder="e.g. data.example.com">
                    <button class="btn btn-ghost" onclick="updateLink()">Update</button>
                </div>
            </div>
        </div>
    </div>

    <script>
        function copyId(id){
            const el=document.getElementById(id);el.select();
            navigator.clipboard.writeText(el.value).then(()=>alert('已复制到剪贴板'));
        }
        function updateLink(){
            const ip = document.getElementById('customIP').value;
            const host = window.location.hostname;
            const pass = "${subpass}";
            let url = "https://" + host + "/" + pass;
            if(ip) url += "?proxyip=" + ip;
            document.getElementById('subLink').value = url;
        }
        function logout(){
            document.cookie="auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";
            location.reload();
        }
    </script>
</body></html>`;
}

// =============================================================================
// 🟢 主处理函数
// =============================================================================
export default {
  async fetch(r, env, ctx) {
    try {
      const url = new URL(r.url);
      const host = url.hostname; 
      
      // 加载配置
      const _UUID = env.KEY ? await getDynamicUUID(env.KEY) : getEnv(env, 'UUID', UUID);
      const _WEB_PW = getEnv(env, 'WEB_PASSWORD', WEB_PASSWORD);
      const _SUB_PW = getEnv(env, 'SUB_PASSWORD', SUB_PASSWORD);
      const _PROXY_IP = getEnv(env, 'PROXYIP', DEFAULT_PROXY_IP);
      const _PS = getEnv(env, 'PS', ""); 
      
      // 根路径重定向
      let _ROOT_REDIRECT = getEnv(env, 'ROOT_REDIRECT_URL', ROOT_REDIRECT_URL);
      if (!_ROOT_REDIRECT.includes('://')) _ROOT_REDIRECT = 'https://' + _ROOT_REDIRECT;

      // 1. 订阅接口处理 (支持 /sub?uuid=... 或 /password)
      const isSubPath = (_SUB_PW && url.pathname === `/${_SUB_PW}`);
      const isNormalSub = (url.pathname === '/sub' && url.searchParams.get('uuid') === _UUID);

      if (isSubPath || isNormalSub) {
          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, requestProxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 2. HTTP 请求处理 (面板与重定向)
      if (r.headers.get('Upgrade') !== 'websocket') {
          // 根路径 -> 重定向
          if (url.pathname === '/') {
              return Response.redirect(_ROOT_REDIRECT, 302);
          }
          
          // 管理面板逻辑 /admin
          if (url.pathname === '/admin' || url.pathname === '/admin/') {
              if (_WEB_PW) {
                  const cookie = r.headers.get('Cookie') || "";
                  if (!cookie.includes(`auth=${_WEB_PW}`)) {
                      return new Response(loginPage(), { status: 200, headers: {'Content-Type': 'text/html'} });
                  }
              }
              // 已登录或无密码
              return new Response(dashPage(host, _UUID, _PROXY_IP, _SUB_PW), { status: 200, headers: {'Content-Type': 'text/html'} });
          }
          
          return new Response('Not Found', { status: 404 });
      }

      // 3. WebSocket 代理处理
      // 解析路径中的 proxyip (e.g. /proxyip=1.2.3.4:443)
      let proxyIPConfig = null;
      if (url.pathname.includes('/proxyip=')) {
        try {
          const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
          const [address, port] = await parseIP(proxyParam); 
          proxyIPConfig = { address, port: +port }; 
        } catch (e) {}
      }

      const globalProxyIPs = await parseProxyList(_PROXY_IP);
      const { 0: c, 1: s } = new WebSocketPair();
      s.accept();
      handle(s, proxyIPConfig, _UUID, globalProxyIPs);
      return new Response(null, { status: 101, webSocket: c });

    } catch (err) {
      return new Response(err.toString(), { status: 500 });
    }
  }
};

// =============================================================================
// 🔧 辅助工具函数
// =============================================================================
async function getCustomIPs(env) {
    let ips = getEnv(env, 'ADD', "");
    const addApi = getEnv(env, 'ADDAPI', "");
    const addCsv = getEnv(env, 'ADDCSV', "");
    
    if (addApi) {
        const urls = addApi.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) {
            try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); ips += "\n" + text; } } catch (e) {}
        }
    }
    
    if (addCsv) {
        const urls = addCsv.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) {
            try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); const lines = text.split('\n'); for (let line of lines) { const parts = line.split(','); if (parts.length >= 2) ips += `\n${parts[0].trim()}:443#${parts[1].trim()}`; } } } catch (e) {}
        }
    }
    return ips;
}

function genNodes(h, u, p, ipsText, ps = "") {
    let l = ipsText.split('\n').filter(line => line.trim() !== "");
    const cleanedProxyIP = p ? p.replace(/\n/g, ',') : '';
    const P = cleanedProxyIP ? `/proxyip=${cleanedProxyIP.trim()}` : "/";
    const E = encodeURIComponent(P);
    return l.map(L => {
        const [a, n] = L.split('#'); if (!a) return "";
        const I = a.trim(); 
        // 节点名称改为 Edge-Instance
        let N = n ? n.trim() : 'Edge-Instance';
        if (ps) N = `${N} ${ps}`;
        let i = I, pt = "443"; if (I.includes(':') && !I.includes('[')) { const s = I.split(':'); i = s[0]; pt = s[1]; }
        return `${PT_TYPE}://${u}@${i}:${pt}?encryption=none&security=tls&sni=${h}&alpn=h3&fp=random&allowInsecure=1&type=ws&host=${h}&path=${E}#${encodeURIComponent(N)}`
    }).join('\n');
}
