import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域 (优先级：环境变量 > 代码硬编码)
// =============================================================================
const UUID = ""; // 请替换为你的 UUID
const WEB_PASSWORD = "";  // 管理面板登录密码
const SUB_PASSWORD = "";  // 订阅路径密码
const DEFAULT_PROXY_IP = "";  // 默认 ProxyIP (支持多行/逗号分隔)
const ROOT_REDIRECT_URL = ""; // 根路径重定向地址
const DEFAULT_CONVERTER = "https://subapi.cmliussss.net";  // 订阅转换后端
const CLASH_CONFIG = "https://raw.githubusercontent.com/cmliu/ACL4SSR/main/Clash/config/ACL4SSR_Online_Full_MultiMode.ini";
const SINGBOX_CONFIG_V12 = "https://raw.githubusercontent.com/sinspired/sub-store-template/main/1.12.x/sing-box.json";

// =============================================================================
// ⚡️ 核心逻辑区
// =============================================================================

// 简化的环境变量获取 (仅读取 Env)
async function getSafeEnv(env, key, fallback) {
    if (env[key] && env[key].trim() !== "") return env[key];
    return fallback;
}

// ProxyIP 列表解析
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

const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

// IP 解析工具
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

// 内存池
class Pool{constructor(){this.b=new ArrayBuffer(16384);this.p=0;this.l=[];this.m=8}alloc(s){if(s<=4096&&s<=16384-this.p){const v=new Uint8Array(this.b,this.p,s);this.p+=s;return v}const r=this.l.pop();return r&&r.byteLength>=s?new Uint8Array(r.buffer,0,s):new Uint8Array(s)}free(b){if(b.buffer===this.b)this.p=Math.max(0,this.p-b.length);else if(this.l.length<this.m&&b.byteLength>=1024)this.l.push(b)}reset(){this.p=0;this.l=[]}}

// 动态 UUID 生成
async function getDynamicUUID(key, refresh = 86400) {
    const time = Math.floor(Date.now() / 1000 / refresh);
    const msg = new TextEncoder().encode(`${key}-${time}`);
    const hash = await crypto.subtle.digest('SHA-256', msg);
    const b = new Uint8Array(hash);
    return [...b.slice(0, 16)].map(n => n.toString(16).padStart(2, '0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/, '$1-$2-$3-$4-$5');
}

const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

// WebSocket 处理逻辑
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
    try { while (1) { if (pb > 2097152) { await new Promise(r => setTimeout(r, 100));
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
  
  const cn = async () => {
    // 1. 尝试直连
    try {
        const direct = connect({ hostname: inf.host, port: inf.port });
        await direct.opened;
        return direct;
    } catch (e) {}

    // 2. 尝试指定 ProxyIP
    if (pc && pc.address) {
        try {
            const specific = connect({ hostname: pc.address, port: pc.port });
            await specific.opened;
            return specific;
        } catch (e) {}
    }

    // 3. 轮询 ProxyIP 列表
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
  return } if (cnt >= 24) { cln(); ws.close(1011); return } if (con) return; cnt++;
  let d = Math.min(50 * Math.pow(1.5, cnt - 1), 3000) * (1.5 - scr * 0.5); d = Math.max(50, Math.floor(d));
  try { csk(); if (pb > 4194304) while (pb > 2097152 && pd.length > 5) { const k = pd.shift();
  pb -= k.length; pool.free(k) } await new Promise(r => setTimeout(r, d)); con = true; s = await cn();
  w = s.writable.getWriter(); r = s.readable.getReader(); con = false; cnt = 0; scr = Math.min(1, scr + 0.15);
  stl = 0; lact = Date.now(); rdL(); wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2);
  if (cnt < 24 && ws.readyState === 1) setTimeout(rcn, 500); else { cln(); ws.close(1011) } } };
  const stT = () => { tm.ka = setInterval(async () => { if (!con && w && Date.now() - lact > 15000) try { await w.write(new Uint8Array(0)); lact = Date.now() } catch { rcn() } }, 5000);
  tm.hc = setInterval(() => { if (!con && st.t > 0 && Date.now() - lact > 8000) { stl++; if (stl >= 12) { if (cnt < 24) { stl = 0; rcn() } else { cln(); ws.close(1011) } } } }, 4000) };
  const csk = () => { rd = false; wt = false; try { w?.releaseLock(); r?.releaseLock();
  s?.close() } catch { } }; 
  const cln = () => { Object.values(tm).forEach(clearInterval); csk(); while (pd.length) pool.free(pd.shift()); pb = 0;
  st = { t: 0, c: 0, ts: Date.now() }; md = 'buf'; asz = 0; tp = [];
  pool.reset() };
  ws.addEventListener('message', async e => { try { if (fst) { fst = false; const b = new Uint8Array(e.data); if (buildUUID(b, 1).toLowerCase() !== uuid.toLowerCase()) throw 0; ws.send(new Uint8Array([0, 0])); const { host, port, payload } = extractAddr(b); inf = { host, port }; con = true; if (payload.length) { const z = pool.alloc(payload.length); z.set(payload); pd.push(z); pb += z.length } stT(); est() } else { lact = Date.now(); if (pb > 4194304) return; const z = pool.alloc(e.data.byteLength); z.set(new Uint8Array(e.data)); pd.push(z); pb += z.length } } catch { cln(); ws.close(1006) } });
  ws.addEventListener('close', cln); ws.addEventListener('error', cln)
};

// 登录页面
function loginPage() {
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Worker 登录</title>
    <style>
        body { font-family: system-ui; background: #0f172a; color: white; display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; }
        .card { background: #1e293b; padding: 2rem; border-radius: 1rem; box-shadow: 0 10px 15px -3px rgba(0,0,0,0.5); text-align: center; width: 100%; max-width: 320px; }
        input { width: 100%; padding: 0.75rem; margin: 1rem 0; border-radius: 0.5rem; border: 1px solid #334155; background: #0f172a; color: white; box-sizing: border-box; }
        button { width: 100%; padding: 0.75rem; background: #3b82f6; color: white; border: none; border-radius: 0.5rem; cursor: pointer; font-weight: bold; }
        button:hover { background: #2563eb; }
    </style>
</head>
<body>
    <div class="card">
        <h2>🔒 访问受限</h2>
        <input type="password" id="pwd" placeholder="输入密码" onkeypress="if(event.keyCode===13)v()">
        <button onclick="v()">验证</button>
    </div>
    <script>
        function v(){
            const p = document.getElementById("pwd").value;
            document.cookie = "auth=" + p + "; path=/; Max-Age=31536000";
            location.reload();
        }
    </script>
</body>
</html>`;
}

// 简化的仪表盘 (移除了统计、日志、封禁管理)
function dashPage(host, uuid, subpass) {
    const defaultSubLink = `https://${host}/${subpass}`;
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Worker 极简面板</title>
    <link href="https://cdn.jsdelivr.net/npm/remixicon@3.5.0/fonts/remixicon.css" rel="stylesheet">
    <style>
        body { background: #0f172a; color: #f8fafc; font-family: system-ui; display: flex; justify-content: center; min-height: 100vh; margin: 0; padding: 20px; box-sizing: border-box; }
        .container { width: 100%; max-width: 600px; display: flex; flex-direction: column; gap: 20px; }
        .card { background: #1e293b; border: 1px solid #334155; border-radius: 16px; padding: 24px; }
        h2 { margin: 0 0 15px 0; font-size: 1.2rem; color: #3b82f6; display: flex; align-items: center; gap: 10px; }
        .input-group { display: flex; gap: 10px; margin-bottom: 15px; }
        input { flex: 1; padding: 10px; background: #0f172a; border: 1px solid #334155; border-radius: 8px; color: #94a3b8; font-family: monospace; }
        button { padding: 10px 20px; background: #3b82f6; color: white; border: none; border-radius: 8px; cursor: pointer; font-weight: 600; display: flex; align-items: center; gap: 5px; }
        button:hover { background: #2563eb; }
        .info-row { display: flex; justify-content: space-between; padding: 10px 0; border-bottom: 1px solid #334155; font-size: 0.9rem; }
        .info-row:last-child { border-bottom: none; }
        .label { color: #94a3b8; }
        .val { font-family: monospace; }
    </style>
</head>
<body>
    <div class="container">
        <div class="card">
            <h2><i class="ri-radar-fill"></i> 系统状态</h2>
            <div class="info-row"><span class="label">运行状态</span><span class="val" style="color:#10b981">Active</span></div>
            <div class="info-row"><span class="label">当前 UUID</span><span class="val">${uuid}</span></div>
            <div class="info-row"><span class="label">当前域名</span><span class="val">${host}</span></div>
        </div>

        <div class="card">
            <h2><i class="ri-link-m"></i> 订阅管理</h2>
            <p style="color:#94a3b8; font-size:0.9rem; margin-bottom:10px">通用订阅链接 (Clash/Sing-box/V2Ray)</p>
            <div class="input-group">
                <input type="text" id="subLink" value="${defaultSubLink}" readonly onclick="this.select()">
                <button onclick="copy('subLink')"><i class="ri-file-copy-line"></i> 复制</button>
            </div>
        </div>
        
        <button onclick="logout()" style="background:#ef4444; width:100%; justify-content:center"><i class="ri-shut-down-line"></i> 退出登录</button>
    </div>

    <script>
        function copy(id) {
            const el = document.getElementById(id);
            el.select();
            navigator.clipboard.writeText(el.value).then(() => alert('已复制到剪贴板'));
        }
        function logout() {
            document.cookie = "auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";
            location.reload();
        }
    </script>
</body>
</html>`;
}

// 主入口
export default {
  async fetch(r, env, ctx) {
    try {
      const url = new URL(r.url);
      const host = url.hostname; 
      
      // 读取配置
      const _UUID = env.KEY ? await getDynamicUUID(env.KEY) : (await getSafeEnv(env, 'UUID', UUID));
      const _WEB_PW = await getSafeEnv(env, 'WEB_PASSWORD', WEB_PASSWORD);
      const _SUB_PW = await getSafeEnv(env, 'SUB_PASSWORD', SUB_PASSWORD);
      const _PROXY_IP = await getSafeEnv(env, 'PROXYIP', DEFAULT_PROXY_IP);
      const _PS = await getSafeEnv(env, 'PS', "");
      
      // 根路径重定向
      let _ROOT_REDIRECT = await getSafeEnv(env, 'ROOT_REDIRECT_URL', ROOT_REDIRECT_URL);
      if (url.pathname === '/' && r.headers.get('Upgrade') !== 'websocket') {
          if (_ROOT_REDIRECT && !_ROOT_REDIRECT.startsWith('http')) _ROOT_REDIRECT = 'https://' + _ROOT_REDIRECT;
          if (_ROOT_REDIRECT) return Response.redirect(_ROOT_REDIRECT, 302);
      }

      // 1. 订阅接口处理
      if (_SUB_PW && url.pathname === `/${_SUB_PW}`) {
          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, requestProxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 2. 常规订阅处理
      if (url.pathname === '/sub') {
          const requestUUID = url.searchParams.get('uuid');
          if (requestUUID?.toLowerCase() !== _UUID.toLowerCase()) return new Response('Invalid UUID', { status: 403 });
          
          let proxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, proxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 3. 管理面板 (仅 /admin 路径)
      if (url.pathname === '/admin' && r.headers.get('Upgrade') !== 'websocket') {
        const noCacheHeaders = { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' };
        
        let hasPassword = !!_WEB_PW;
        let isAuthorized = false;
        if (hasPassword) {
            const cookie = r.headers.get('Cookie') || "";
            const match = cookie.match(/auth=([^;]+)/);
            if (match && match[1] === _WEB_PW) isAuthorized = true;
        } else {
            // 如果未设置密码，默认允许访问（或者你可以改为默认禁止）
            isAuthorized = true; 
        }
          
        if (hasPassword && !isAuthorized) {
            return new Response(loginPage(), { status: 200, headers: noCacheHeaders });
        }
        return new Response(dashPage(url.hostname, _UUID, _SUB_PW), { status: 200, headers: noCacheHeaders });
      }

      // 4. WebSocket 代理处理
      if (r.headers.get('Upgrade') === 'websocket') {
          let proxyIPConfig = null;
          // 尝试从路径解析 proxyip
          if (url.pathname.includes('/proxyip=')) {
            try {
              const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
              const [address, port] = await parseIP(proxyParam); 
              proxyIPConfig = { address, port: +port }; 
            } catch (e) {}
          }

          // 准备全局 ProxyIP 列表
          const globalProxyIPs = await parseProxyList(_PROXY_IP);
          const { 0: c, 1: s } = new WebSocketPair();
          s.accept();
          
          // 启动处理
          handle(s, proxyIPConfig, _UUID, globalProxyIPs);
          return new Response(null, { status: 101, webSocket: c });
      }

      // 其他路径返回 404
      if (url.pathname !== '/' && url.pathname !== '/favicon.ico') {
          return new Response('Not Found', { status: 404 });
      }
      return new Response(null, { status: 404 });

    } catch (err) {
      return new Response(err.toString(), { status: 500 });
    }
  }
};

// 辅助函数：获取自定义 IP 列表
async function getCustomIPs(env) {
    let ips = await getSafeEnv(env, 'ADD', "");
    const addApi = await getSafeEnv(env, 'ADDAPI', "");
    const addCsv = await getSafeEnv(env, 'ADDCSV', "");
    
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

// 辅助函数：生成节点文本
function genNodes(h, u, p, ipsText, ps = "") {
    let l = ipsText.split('\n').filter(line => line.trim() !== "");
    const cleanedProxyIP = p ? p.replace(/\n/g, ',') : '';
    const P = cleanedProxyIP ? `/proxyip=${cleanedProxyIP.trim()}` : "/";
    const E = encodeURIComponent(P);
    return l.map(L => {
        const [a, n] = L.split('#'); if (!a) return "";
        const I = a.trim(); 
        let N = n ? n.trim() : 'Worker-Node';
        if (ps) N = `${N} ${ps}`;
        let i = I, pt = "443"; if (I.includes(':') && !I.includes('[')) { const s = I.split(':'); i = s[0]; pt = s[1]; }
        return `${PT_TYPE}://${u}@${i}:${pt}?encryption=none&security=tls&sni=${h}&alpn=h3&fp=random&allowInsecure=1&type=ws&host=${h}&path=${E}#${encodeURIComponent(N)}`
    }).join('\n');
}
