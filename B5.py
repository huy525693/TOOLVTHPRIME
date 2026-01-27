"""
GOD LOGIC V3.0
UPDATE VIP100, BPP SCORE
ADMIN: KHANHHUY (GITHUB: HUY525693)
"""

from __future__ import annotations
import json
import sys
import time
import threading
import random
import logging
import math
import re
from collections import defaultdict, deque
from datetime import datetime
from urllib.parse import urlparse, parse_qs
from typing import Any, Dict, Tuple, Optional, List, Union

import pytz
import requests
import websocket
from rich.console import Console, Group
from rich.table import Table
from rich.panel import Panel
from rich.live import Live
from rich.align import Align
from rich.rule import Rule
from rich.text import Text
from rich import box
from rich.layout import Layout

# -------------------- CONFIG & GLOBALS --------------------
console = Console()
tz = pytz.timezone("Asia/Ho_Chi_Minh")

logger = logging.getLogger("escape_vip_ai_rebuild")
logger.setLevel(logging.INFO)
logger.addHandler(logging.FileHandler("escape_vip_ai_rebuild.log", encoding="utf-8"))

# Endpoints (config)
BET_API_URL = "https://api.escapemaster.net/escape_game/bet"
WS_URL = "wss://api.escapemaster.net/escape_master/ws"
WALLET_API_URL = "https://wallet.3games.io/api/wallet/user_asset"

HTTP = requests.Session()
try:
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
    adapter = HTTPAdapter(
        pool_connections=20, pool_maxsize=50,
        max_retries=Retry(total=3, backoff_factor=0.2,
                          status_forcelist=(500, 502, 503, 504))
    )
    HTTP.mount("https://", adapter)
    HTTP.mount("http://", adapter)
except Exception:
    pass

ROOM_NAMES = {
    1: "📦 Nhà kho", 2: "🪑 Phòng họp", 3: "👔 Phòng giám đốc", 4: "💬 Phòng trò chuyện",
    5: "🎥 Phòng giám sát", 6: "🏢 Văn phòng", 7: "💰 Phòng tài vụ", 8: "👥 Phòng nhân sự"
}
ROOM_ORDER = [1, 2, 3, 4, 5, 6, 7, 8]

# runtime state
USER_ID: Optional[int] = None
SECRET_KEY: Optional[str] = None
issue_id: Optional[int] = None
issue_start_ts: Optional[float] = None
count_down: Optional[int] = None
killed_room: Optional[int] = None
round_index: int = 0

room_state: Dict[int, Dict[str, Any]] = {r: {"players": 0, "bet": 0} for r in ROOM_ORDER}
room_stats: Dict[int, Dict[str, Any]] = {r: {"kills": 0, "survives": 0, "last_kill_round": None, "last_players": 0, "last_bet": 0} for r in ROOM_ORDER}

predicted_room: Optional[int] = None
last_killed_room: Optional[int] = None
prediction_locked: bool = False

# *** GODMODE UPGRADE: Track last 20 kills và Pattern Tracker ***
game_kill_history: deque = deque(maxlen=20)
game_kill_pattern_tracker: Dict[str, Any] = {
    "kill_counts": defaultdict(int),
    "kill_seq": deque(maxlen=5),
    "last_kill_ts": time.time(),
}

# balances & pnl
current_build: Optional[float] = None
current_usdt: Optional[float] = None
current_world: Optional[float] = None
last_balance_ts: Optional[float] = None
last_balance_val: Optional[float] = None
starting_balance: Optional[float] = None
cumulative_profit: float = 0.0

# streaks
win_streak: int = 0
lose_streak: int = 0
max_win_streak: int = 0
max_lose_streak: int = 0

# betting
base_bet: float = 1.0
multiplier: float = 2.0
current_bet: Optional[float] = None
run_mode: str = "AUTO"

# AUTO or STAT
bet_rounds_before_skip: int = 0
_rounds_placed_since_skip: int = 0
skip_next_round_flag: bool = False

bet_history: deque = deque(maxlen=500)
bet_sent_for_issue: set = set()

# new controls
pause_after_losses: int = 0
_skip_rounds_remaining: int = 0
profit_target: Optional[float] = None
stop_when_profit_reached: bool = False
stop_loss_target: Optional[float] = None
stop_when_loss_reached: bool = False
stop_flag: bool = False

# UI / timing
ui_state: str = "IDLE"
analysis_start_ts: Optional[float] = None
analysis_blur: bool = False
# ws/poll
last_msg_ts: float = time.time()
last_balance_fetch_ts: float = 0.0
BALANCE_POLL_INTERVAL: float = 4.0
_ws: Dict[str, Any] = {"ws": None}

# selection config (used by algorithms)
SELECTION_CONFIG = {
    "max_bet_allowed": float("inf"),
    "max_players_allowed": 9999,
    "avoid_last_kill": True,
    # === NEW SMART FILTERS ===
    "max_recent_kills": 3,
    "min_survive_rate": 0.55,
    "bet_management_strategy": "MARTINGALE",
    "bpp_trap_low": 500.0,
    "bpp_trap_high": 4000.0,
}

# GODMODE chỉ có một chế độ
SELECTION_MODES = {
    "GODMODE": "CHIẾN THẦN PROMAX - HÀO QUANG CỦA THẦN"
}
settings = {"algo": "GODMODE"}

# Spinner vàng với biểu tượng god, ngôi sao
_spinner = ["🌟", "⭐", "👑", "🔥", "✨"]

_num_re = re.compile(r"-?\d+[\d,]*\.?\d*")

# Chủ đề màu vàng
MAIN_COLOR = "yellow1"
ACCENT_COLOR = "orange1"
TEXT_COLOR = "bold white"
SUCCESS_COLOR = "bold #00ff00"
FAILURE_COLOR = "bold #ff0000"
PENDING_COLOR = "bold #ffff00"

# -------------------- UTILITIES --------------------

def log_debug(msg: str):
    try:
        logger.debug(msg)
    except Exception:
        pass


def _parse_number(x: Any) -> Optional[float]:
    if x is None:
        return None
    if isinstance(x, (int, float)):
        return float(x)
    s = str(x)
    m = _num_re.search(s)
    if not m:
        return None
    token = m.group(0).replace(",", "")
    try:
        return float(token)
    except Exception:
        return None


def human_ts() -> str:
    return datetime.now(tz).strftime("%Y-%m-%d %H:%M:%S")


def safe_input(prompt: str, default=None, cast=None):
    try:
        s = input(prompt).strip()
    except EOFError:
        return default
    if s == "":
        return default
    if cast:
        try:
            return cast(s)
        except Exception:
            return default
    return s

# -------------------- BALANCE PARSING & FETCH --------------------
def _parse_balance_from_json(j: Dict[str, Any]) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    if not isinstance(j, dict):
        return None, None, None
    build = None
    world = None
    usdt = None

    data = j.get("data") if isinstance(j.get("data"), dict) else j
    if isinstance(data, dict):
        cwallet = data.get("cwallet") if isinstance(data.get("cwallet"), dict) else None
        if cwallet:
            for key in ("ctoken_contribute", "ctoken", "build", "balance", "amount"):
                if key in cwallet and build is None:
                    build = _parse_number(cwallet.get(key))
        for k in ("build", "ctoken", "ctoken_contribute"):
            if build is None and k in data:
                build = _parse_number(data.get(k))
        for k in ("usdt", "kusdt", "usdt_balance"):
            if usdt is None and k in data:
                usdt = _parse_number(data.get(k))
        for k in ("world", "xworld"):
            if world is None and k in data:
                world = _parse_number(data.get(k))

    found = []

    def walk(o: Any, path=""):
        if isinstance(o, dict):
            for kk, vv in o.items():
                nk = (path + "." + str(kk)).strip(".")
                if isinstance(vv, (dict, list)):
                    walk(vv, nk)
                else:
                    n = _parse_number(vv)
                    if n is not None:
                        found.append((nk.lower(), n))
        elif isinstance(o, list):
            for idx, it in enumerate(o):
                walk(it, f"{path}[{idx}]")

    walk(j)

    for k, n in found:
        if build is None and any(x in k for x in ("ctoken", "build", "contribute", "balance")):
            build = n
        if usdt is None and "usdt" in k:
            usdt = n
        if world is None and any(x in k for x in ("world", "xworld")):
            world = n

    return build, world, usdt


def balance_headers_for(uid: Optional[int] = None, secret: Optional[str] = None) -> Dict[str, str]:
    h = {
        "accept": "*/*",
        "accept-language": "vi,en;q=0.9",
        "cache-control": "no-cache",
        "country-code": "vn",
        "origin": "https://xworld.info",
        "pragma": "no-cache",
        "referer": "https://xworld.info/",
        "user-agent": "Mozilla/5.0 (Linux; Android 6.0; Nexus 5) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/137.0.0.0 Mobile Safari/537.36",
        "user-login": "login_v2",
        "xb-language": "vi-VN",
    }
    if uid is not None:
        h["user-id"] = str(uid)
    if secret:
        h["user-secret-key"] = str(secret)
    return h


def fetch_balances_3games(retries=2, timeout=6, params=None, uid=None, secret=None):
    global current_build, current_usdt, current_world, last_balance_ts
    global starting_balance, last_balance_val, cumulative_profit

    uid = uid or USER_ID
    secret = secret or SECRET_KEY
    payload = {"user_id": int(uid) if uid is not None else None, "source": "home"}

    attempt = 0
    while attempt <= retries:
        attempt += 1
        try:
            r = HTTP.post(
                WALLET_API_URL,
                json=payload,
                headers=balance_headers_for(uid, secret),
                timeout=timeout,
            )
            r.raise_for_status()
            j = r.json()

            build, world, usdt = _parse_balance_from_json(j)

            if build is not None:
                if last_balance_val is None:
                    starting_balance = build
                    last_balance_val = build
                else:
                    delta = float(build) - float(last_balance_val)
                    if abs(delta) > 0:
                        cumulative_profit += delta
                        last_balance_val = build
                current_build = build
            if usdt is not None:
                current_usdt = usdt
            if world is not None:
                current_world = world

            last_balance_ts = time.time()
            return current_build, current_world, current_usdt

        except Exception as e:
            log_debug(f"wallet fetch attempt {attempt} error: {e}")
            time.sleep(min(0.6 * attempt, 2))

    return current_build, current_world, current_usdt


# -------------------- GODMODE ENSEMBLE SELECTION --------------------

def _room_features(rid: int) -> Dict[str, float]:
    global game_kill_history, round_index, room_state, room_stats, last_killed_room, game_kill_pattern_tracker
    
    st = room_state.get(rid, {})
    stats = room_stats.get(rid, {})
    players = float(st.get("players", 0))
    bet = float(st.get("bet", 0))
    bet_per_player = (bet / players) if players > 0 else 0.0
    kill_count = float(stats.get("kills", 0))
    survive_count = float(stats.get("survives", 0))
    total_rounds = kill_count + survive_count
    kill_rate = (kill_count + 1.0) / (total_rounds + 2.0) if total_rounds > 0 else 0.5
    survive_score = 1.0 - kill_rate
    
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    
    players_norm = players / max(1.0, all_players)
    bet_norm = bet / max(1.0, all_bet)
    contrarian_score = 1.0 - (players_norm + bet_norm) / 2.0

    recent_pen = 0.0
    for i, rec in enumerate(reversed(list(bet_history))):
        if i >= 10: break
        if rec.get("room") == rid and rec.get("result") == "Thua":
            recent_pen += 0.15 * (1.0 / (i + 1))
    
    last_pen = 0.0
    if last_killed_room == rid and SELECTION_CONFIG.get("avoid_last_kill", True):
        last_pen = 0.45

    total_rounds_stats = sum(r['kills'] + r['survives'] for r in room_stats.values())
    safety_score = 0.5
    if total_rounds_stats > 0:
        safety_score = 1.0 - (kill_count / max(1, total_rounds_stats / 8))

    last_kill_round = stats.get("last_kill_round")
    cold_room_score = 0.0
    min_rounds_safe = 10.0
    if last_kill_round is None:
        cold_room_score = 1.0
    else:
        delta = round_index - last_kill_round
        cold_room_score = min(1.0, delta / min_rounds_safe)

    recent_kills = game_kill_history.count(rid)
    freq_penalty = min(1.0, recent_kills / SELECTION_CONFIG.get("max_recent_kills", 3.0))

    bpp_score = 0.0
    min_h = SELECTION_CONFIG.get("bpp_trap_low", 500.0)
    max_h = SELECTION_CONFIG.get("bpp_trap_high", 4000.0)
    
    if bet_per_player < min_h:
        bpp_score = max(0.0, bet_per_player / min_h)
    elif bet_per_player > max_h:
        bpp_score = max(0.0, 1.0 - (bet_per_player - max_h) / max_h)
    else:
        bpp_score = 1.0
        
    pattern_penalty = 0.0
    kill_seq = game_kill_pattern_tracker.get("kill_seq", deque())
    
    if len(kill_seq) >= 3:
        if rid == kill_seq[-3] and rid != kill_seq[-2]:
             pattern_penalty = max(pattern_penalty, 0.6)
        
        if len(kill_seq) == 5 and all(r == rid for r in kill_seq):
             pattern_penalty = max(pattern_penalty, 0.9)

    avg_bpp_all = all_bet / max(1.0, all_players)
    bpp_relative_score = 1.0 - abs(bet_per_player - avg_bpp_all) / max(1.0, avg_bpp_all * 2)
        
    return {
        "players": players, "bet": bet, "bet_per_player": bet_per_player,
        "players_norm": players_norm, "bet_norm": bet_norm,
        "contrarian_score": contrarian_score,
        "kill_rate": kill_rate, "survive_score": survive_score,
        "safety_score": safety_score,
        "recent_pen": recent_pen, "last_pen": last_pen,
        "cold_room_score": cold_room_score,
        "freq_penalty": freq_penalty,
        "bpp_score": bpp_score,
        "pattern_penalty": pattern_penalty,
        "bpp_relative_score": bpp_relative_score,
    }


def choose_room_godmode() -> Tuple[int, str]:
    """
    GODMODE - Ensemble prediction với bộ lọc thông minh và kiểm soát rủi ro.
    """
    global game_kill_history, round_index, room_state, room_stats, last_killed_room
    
    features = {}
    
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    avg_players = all_players / max(1, len(ROOM_ORDER))
    avg_bet = all_bet / max(1, len(ROOM_ORDER))
    avg_bpp_all = all_bet / max(1, all_players)

    player_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("players", 0), reverse=True)
    bet_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("bet", 0), reverse=True)
    
    recent_10_kills = list(game_kill_history)[-10:]
    low_zone_kills = sum(1 for k in recent_10_kills if k in [1, 2, 3, 4])
    high_zone_kills = sum(1 for k in recent_10_kills if k in [5, 6, 7, 8])

    for r in ROOM_ORDER:
        f = _room_features(r)

        f['player_rank'] = player_ranks_sorted.index(r) + 1
        f['bet_rank'] = bet_ranks_sorted.index(r) + 1
        
        whale_bpp_threshold = max(3000.0, avg_bpp_all * 5.0)
        f['whale_trap_score'] = 0.0
        if 0 < f['players'] <= 3 and f['bet_per_player'] > whale_bpp_threshold:
            f['whale_trap_score'] = 1.0
        
        f['decoy_trap_score'] = 1.0 if f['player_rank'] in [2, 3] else 0.0
        
        f['zone_penalty'] = 0.0
        my_zone = 'low' if r <= 4 else 'high'
        if my_zone == 'low' and low_zone_kills > high_zone_kills:
            f['zone_penalty'] = min(1.0, (low_zone_kills - high_zone_kills) / 5.0)
        elif my_zone == 'high' and high_zone_kills > low_zone_kills:
            f['zone_penalty'] = min(1.0, (high_zone_kills - low_zone_kills) / 5.0)

        features[r] = f

    filtered_cand = []
    
    for r in ROOM_ORDER:
        f = features[r]
        
        if SELECTION_CONFIG.get("avoid_last_kill", True) and last_killed_room == r:
            continue
        
        if f["survive_score"] < SELECTION_CONFIG.get("min_survive_rate", 0.55):
            continue
        
        if (f["players"] > avg_players * 1.8) and (f["bet"] > avg_bet * 1.8):
            continue

        if f["freq_penalty"] > 0.8:
            continue
            
        if f["bpp_score"] < 0.3:
            continue

        if f["pattern_penalty"] > 0.5:
            continue
            
        if f['whale_trap_score'] > 0.5:
            continue
        
        if f['zone_penalty'] > 0.8:
            continue

        filtered_cand.append(r)

    if not filtered_cand:
        fallback_scores = {r: _room_features(r)["kill_rate"] for r in ROOM_ORDER if r != last_killed_room}
        if not fallback_scores:
             fallback_scores = {r: _room_features(r)["kill_rate"] for r in ROOM_ORDER}
             
        best_room = min(fallback_scores.items(), key=lambda x: x[1])[0]
        return best_room, "GODMODE_FALLBACK"

    WEIGHTS = {
        "safety_contrarian": 1.5,
        "safety_bpp_health": 1.2,
        "safety_cold_room": 1.0,
        "safety_survive_hist": 0.5,
        "safety_bpp_relative": 0.3,
        "trap_decoy": 2.5,
        "trap_whale": 2.5,
        "trap_bpp_dev": 1.5,
        "trap_freq": 1.5,
        "trap_pattern": 1.2,
        "trap_zone": 1.0,
        "trap_last_kill": 0.8,
    }
    
    agg_scores = {r: 0.0 for r in filtered_cand}
    
    for r in filtered_cand:
        f = features[r]
        
        safety_score = 0.0
        safety_score += WEIGHTS["safety_contrarian"] * f["contrarian_score"]
        safety_score += WEIGHTS["safety_bpp_health"] * f["bpp_score"]
        safety_score += WEIGHTS["safety_cold_room"] * f["cold_room_score"]
        safety_score += WEIGHTS["safety_survive_hist"] * f["survive_score"]
        safety_score += WEIGHTS["safety_bpp_relative"] * f["bpp_relative_score"]
        
        trap_score = 0.0
        trap_score += WEIGHTS["trap_decoy"] * f["decoy_trap_score"]
        trap_score += WEIGHTS["trap_whale"] * f["whale_trap_score"]
        trap_score += WEIGHTS["trap_freq"] * f["freq_penalty"]
        trap_score += WEIGHTS["trap_pattern"] * f["pattern_penalty"]
        trap_score += WEIGHTS["trap_zone"] * f["zone_penalty"]
        trap_score += WEIGHTS["trap_last_kill"] * f["last_pen"]

        final_score = safety_score - trap_score
        agg_scores[r] = final_score

    ranked = sorted(agg_scores.items(), key=lambda kv: (-kv[1], kv[0]))
    best_room = ranked[0][0]
    
    return best_room, "GODMODE"


# -------------------- BETTING HELPERS --------------------

def api_headers() -> Dict[str, str]:
    return {
        "content-type": "application/json",
        "user-agent": "Mozilla/5.0",
        "user-id": str(USER_ID) if USER_ID else "",
        "user-secret-key": SECRET_KEY if SECRET_KEY else ""
    }


def place_bet_http(issue: int, room_id: int, amount: float) -> dict:
    payload = {"asset_type": "BUILD", "user_id": USER_ID, "room_id": int(room_id), "bet_amount": float(amount)}
    try:
        r = HTTP.post(BET_API_URL, headers=api_headers(), json=payload, timeout=6)
        try:
            return r.json()
        except Exception:
            return {"raw": r.text, "http_status": r.status_code}
    except Exception as e:
        return {"error": str(e)}


def record_bet(issue: int, room_id: int, amount: float, resp: dict, algo_used: Optional[str] = None) -> dict:
    now = datetime.now(tz).strftime("%H:%M:%S")
    rec = {
        "issue": issue, "room": room_id, "amount": float(amount), 
        "time": now, "resp": resp, "result": "Đang", 
        "algo": algo_used, "delta": 0.0, "win_streak": win_streak, 
        "lose_streak": lose_streak,
        "killed_room_id": None
    }
    bet_history.append(rec)
    return rec


def place_bet_async(issue: int, room_id: int, amount: float, algo_used: Optional[str] = None):
    def worker():
        console.print(f"[{PENDING_COLOR}]Đang đặt {amount:,.4f} BUILD -> PHÒNG_{room_id} (v{issue}) — Thuật toán: {algo_used}[/]")
        time.sleep(random.uniform(0.02, 0.25))
        res = place_bet_http(issue_id, room_id, amount)
        rec = record_bet(issue_id, room_id, amount, res, algo_used=algo_used)
        
        if isinstance(res, dict) and (res.get("msg") == "ok" or res.get("code") == 0 or res.get("status") in ("ok", 1) or "success" in str(res).lower()):
            bet_sent_for_issue.add(issue_id)
            console.print(f"[{SUCCESS_COLOR}]✅ Đặt thành công {amount:,.4f} BUILD vào PHÒNG_{room_id} (v{issue_id}).[/]")
        else:
            console.print(f"[{FAILURE_COLOR}]❌ Đặt lỗi v{issue_id}: {res}[/]")
            
    threading.Thread(target=worker, daemon=True).start()

# -------------------- LOCK & AUTO-BET --------------------

def lock_prediction_if_needed(force: bool = False):
    global prediction_locked, predicted_room, ui_state, current_bet, _rounds_placed_since_skip, skip_next_round_flag, _skip_rounds_remaining, win_streak, lose_streak
    global current_build
    
    if stop_flag:
        return
    if prediction_locked and not force:
        return
    if issue_id is None:
        return
        
    if _skip_rounds_remaining > 0:
        prediction_locked = True
        ui_state = "IDLE"
        console.print(f"[{ACCENT_COLOR}]⏸️ Đang nghỉ sau khi thua (Còn lại {_skip_rounds_remaining} ván).[/]")
        _skip_rounds_remaining -= 1
        return

    if skip_next_round_flag:
        prediction_locked = True
        ui_state = "IDLE"
        console.print(f"[{ACCENT_COLOR}]⏸️ TẠM DỪNG THEO DÕI SÁT THỦ (Cấu hình SKIP 1 ván).[/]")
        skip_next_round_flag = False
        return
        
    prediction_locked = True
    ui_state = "PREDICTED"
    
    chosen, algo_used = choose_room_godmode()
    predicted_room = chosen
    
    if run_mode == "AUTO":
        bld, _, _ = fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
        if bld is None:
            console.print(f"[{ACCENT_COLOR}]⚠️ Không lấy được số dư trước khi đặt — bỏ qua đặt ván này.[/]")
            prediction_locked = False
            return
            
        if current_bet is None:
            current_bet = base_bet
        
        strategy = SELECTION_CONFIG.get("bet_management_strategy", "MARTINGALE")
        if strategy == "ANTI-MARTINGALE":
            if win_streak > 0:
                current_bet = base_bet + (base_bet * 0.1 * win_streak)
            else:
                current_bet = base_bet
                
        if current_bet < base_bet:
            current_bet = base_bet

        amt = float(current_bet)
        
        if amt <= 0 or amt > current_build:
            console.print(f"[{FAILURE_COLOR}]⚠️ Số tiền đặt không hợp lệ ({amt:,.4f} > {current_build:,.4f}). Bỏ qua.[/]")
            prediction_locked = False
            return
        
        place_bet_async(issue_id, predicted_room, amt, algo_used=algo_used)
        _rounds_placed_since_skip += 1
        
        if bet_rounds_before_skip > 0 and _rounds_placed_since_skip >= bet_rounds_before_skip:
            skip_next_round_flag = True
            _rounds_placed_since_skip = 0

# -------------------- WEBSOCKET HANDLERS --------------------

def safe_send_enter_game(ws):
    if not ws:
        log_debug("safe_send_enter_game: ws None")
        return
    try:
        payload = {"msg_type": "handle_enter_game", "asset_type": "BUILD", "user_id": USER_ID, "user_secret_key": SECRET_KEY}
        ws.send(json.dumps(payload))
        log_debug("Sent enter_game")
    except Exception as e:
        log_debug(f"safe_send_enter_game err: {e}")


def _extract_issue_id(d: Dict[str, Any]) -> Optional[int]:
    if not isinstance(d, dict):
        return None
    possible = []
    for key in ("issue_id", "issueId", "issue", "id"):
        v = d.get(key)
        if v is not None:
            possible.append(v)
    if isinstance(d.get("data"), dict):
        for key in ("issue_id", "issueId", "issue", "id"):
            v = d["data"].get(key)
            if v is not None:
                possible.append(v)
    for p in possible:
        try:
            return int(p)
        except Exception:
            try:
                return int(str(p))
            except Exception:
                continue
    return None


def on_open(ws):
    _ws["ws"] = ws
    console.print(f"[{SUCCESS_COLOR}]ĐANG TRUY CẬP DỮ LIỆU GAME (GODMODE ON)[/]")
    safe_send_enter_game(ws)


def _background_fetch_balance_after_result():
    try:
        fetch_balances_3games()
    except Exception:
        pass


def _mark_bet_result_from_issue(res_issue: Optional[int], krid: int):
    global current_bet, win_streak, lose_streak, max_win_streak, max_lose_streak, _skip_rounds_remaining, stop_flag, multiplier, base_bet
    if res_issue is None:
        return
        
    rec = None
    for b in reversed(list(bet_history)):
        if b.get("issue") == res_issue:
            rec = b
            break
            
    if rec is None:
        return
        
    try:
        rec["killed_room_id"] = int(krid)
        
        placed_room = int(rec.get("room"))
        placed_amount = float(rec.get("amount"))
        is_win = (placed_room != int(krid))
        
        delta = 0.0
        if is_win:
            rec["result"] = "Thắng"
            delta = placed_amount
            
            if SELECTION_CONFIG.get("bet_management_strategy") == "MARTINGALE":
                 current_bet = base_bet
            
            win_streak += 1
            lose_streak = 0
            if win_streak > max_win_streak:
                max_win_streak = win_streak
                
        else:
            rec["result"] = "Thua"
            delta = -placed_amount
            
            if SELECTION_CONFIG.get("bet_management_strategy") == "MARTINGALE":
                try:
                    current_bet = placed_amount * float(multiplier)
                except Exception:
                    current_bet = base_bet
            else:
                 current_bet = base_bet
                 
            lose_streak += 1
            win_streak = 0
            if lose_streak > max_lose_streak:
                max_lose_streak = lose_streak
                
            if pause_after_losses > 0:
                _skip_rounds_remaining = pause_after_losses
                
        rec["delta"] = delta
        
    except Exception as e:
        log_debug(f"_mark_bet_result_from_issue err: {e}")


def on_message(ws, message):
    global issue_id, count_down, killed_room, round_index, ui_state, analysis_start_ts, issue_start_ts
    global prediction_locked, predicted_room, last_killed_room, last_msg_ts, current_bet
    global win_streak, lose_streak, max_win_streak, max_lose_streak, cumulative_profit, _skip_rounds_remaining, stop_flag, analysis_blur
    global game_kill_history, game_kill_pattern_tracker, room_stats
    
    last_msg_ts = time.time()
    try:
        if isinstance(message, bytes):
            try:
                message = message.decode("utf-8", errors="replace")
            except Exception:
                message = str(message)
        data = None
        try:
            data = json.loads(message)
        except Exception:
            try:
                data = json.loads(message.replace("'", '"'))
            except Exception:
                log_debug(f"on_message non-json: {str(message)[:200]}")
                return

        if isinstance(data, dict) and isinstance(data.get("data"), str):
            try:
                inner = json.loads(data.get("data"))
                merged = dict(data)
                merged.update(inner)
                data = merged
            except Exception:
                pass

        msg_type = data.get("msg_type") or data.get("type") or ""
        msg_type = str(msg_type)
        new_issue = _extract_issue_id(data)

        if msg_type == "notify_issue_stat" or "issue_stat" in msg_type:
            rooms = data.get("rooms") or []
            if not rooms and isinstance(data.get("data"), dict):
                rooms = data["data"].get("rooms", [])
            for rm in (rooms or []):
                try:
                    rid = int(rm.get("room_id") or rm.get("roomId") or rm.get("id"))
                except Exception:
                    continue
                players = int(rm.get("user_cnt") or rm.get("userCount") or 0) or 0
                bet = float(rm.get("total_bet_amount") or rm.get("totalBet") or rm.get("bet") or 0) or 0
                room_state[rid] = {"players": players, "bet": bet}
                room_stats[rid]["last_players"] = players
                room_stats[rid]["last_bet"] = bet
            if new_issue is not None and new_issue != issue_id:
                log_debug(f"New issue: {issue_id} -> {new_issue}")
                issue_id = new_issue
                issue_start_ts = time.time()
                killed_room = None
                prediction_locked = False
                predicted_room = None
                
                if ui_state == "RESULT":
                     round_index += 1
                
                ui_state = "ANALYZING"
                analysis_start_ts = time.time()

        elif msg_type == "notify_count_down" or "count_down" in msg_type:
            count_down_val = data.get("count_down") or data.get("countDown") or data.get("count") or count_down
            try:
                count_val = int(count_down_val)
                count_down = count_val
            except Exception:
                count_val = None
                
            if count_val is not None:
                try:
                    if count_val <= 10 and not prediction_locked:
                        analysis_blur = False
                        lock_prediction_if_needed()
                    elif count_val <= 45:
                        ui_state = "ANALYZING"
                        analysis_start_ts = time.time()
                        analysis_blur = True
                except Exception as e:
                    log_debug(f"Countdown logic error: {e}")

        elif msg_type == "notify_result" or "result" in msg_type:
            kr = data.get("killed_room") if data.get("killed_room") is not None else data.get("killed_room_id")
            if kr is None and isinstance(data.get("data"), dict):
                kr = data["data"].get("killed_room") or data["data"].get("killed_room_id")
                
            if kr is not None:
                try:
                    krid = int(kr)
                except Exception:
                    krid = kr
                killed_room = krid
                last_killed_room = krid
                
                game_kill_history.append(krid)
                game_kill_pattern_tracker["kill_seq"].append(krid)
                game_kill_pattern_tracker["kill_counts"][krid] += 1
                game_kill_pattern_tracker["last_kill_ts"] = time.time()
                
                for rid in ROOM_ORDER:
                    if rid == krid:
                        room_stats[rid]["kills"] += 1
                        room_stats[rid]["last_kill_round"] = round_index
                    else:
                        room_stats[rid]["survives"] += 1

                res_issue = new_issue if new_issue is not None else issue_id
                _mark_bet_result_from_issue(res_issue, krid)
                
                threading.Thread(target=_background_fetch_balance_after_result, daemon=True).start()

            ui_state = "RESULT"

            def _check_stop_conditions():
                global stop_flag, current_build, profit_target, stop_loss_target
                try:
                    if stop_when_profit_reached and profit_target is not None and isinstance(current_build, (int, float)) and current_build >= profit_target:
                        console.print(f"[{SUCCESS_COLOR} on {MAIN_COLOR}]🎉 MỤC TIÊU LÃI ĐẠT: {current_build:,.4f} >= {profit_target:,.4f}. Dừng tool.[/]")
                        stop_flag = True
                        try:
                            wsobj = _ws.get("ws")
                            if wsobj: wsobj.close()
                        except Exception:
                            pass
                    if stop_when_loss_reached and stop_loss_target is not None and isinstance(current_build, (int, float)) and current_build <= stop_loss_target:
                        console.print(f"[{FAILURE_COLOR} on {MAIN_COLOR}]⚠️ STOP-LOSS TRIGGED: {current_build:,.4f} <= {stop_loss_target:,.4f}. Dừng tool.[/]")
                        stop_flag = True
                        try:
                            wsobj = _ws.get("ws")
                            if wsobj: wsobj.close()
                        except Exception:
                            pass
                except Exception as e:
                    log_debug(f"Stop conditions check error: {e}")
                    
            threading.Timer(1.2, _check_stop_conditions).start()

    except Exception as e:
        log_debug(f"on_message err: {e}")


def on_close(ws, code, reason):
    log_debug(f"WS closed: {code} {reason}")


def on_error(ws, err):
    log_debug(f"WS error: {err}")


def start_ws():
    backoff = 0.6
    while not stop_flag:
        try:
            ws_app = websocket.WebSocketApp(WS_URL, on_open=on_open, on_message=on_message, on_close=on_close, on_error=on_error)
            _ws["ws"] = ws_app
            ws_app.run_forever(ping_interval=12, ping_timeout=6)
        except Exception as e:
            log_debug(f"start_ws exception: {e}")
        t = min(backoff + random.random() * 0.5, 30)
        log_debug(f"Reconnect WS after {t}s")
        console.print(f"[{ACCENT_COLOR}]Đã mất kết nối WS. Đang thử kết nối lại sau {t:.1f}s...[/]")
        time.sleep(t)
        backoff = min(backoff * 1.5, 30)

# -------------------- BALANCE POLLER THREAD --------------------

class BalancePoller(threading.Thread):
    def __init__(self, uid: Optional[int], secret: Optional[str], poll_seconds: int = 2, on_balance=None, on_error=None, on_status=None):
        super().__init__(daemon=True)
        self.uid = uid
        self.secret = secret
        self.poll_seconds = max(1, int(poll_seconds))
        self._running = True
        self._last_balance_local: Optional[float] = None
        self.on_balance = on_balance
        self.on_error = on_error
        self.on_status = on_status

    def stop(self):
        self._running = False

    def run(self):
        if self.on_status:
            self.on_status("Kết nối...")
        while self._running and not stop_flag:
            try:
                build, world, usdt = fetch_balances_3games(params={"userId": str(self.uid)} if self.uid else None, uid=self.uid, secret=self.secret)
                if build is None:
                    raise RuntimeError("Không đọc được balance từ response")
                delta = 0.0 if self._last_balance_local is None else (build - self._last_balance_local)
                first_time = (self._last_balance_local is None)
                if first_time or abs(delta) > 0.000001:
                    self._last_balance_local = build
                    if self.on_balance:
                        self.on_balance(float(build), float(delta), {"ts": human_ts()})
                    if self.on_status:
                        self.on_status("Đang theo dõi")
                else:
                    if self.on_status:
                        self.on_status("Đang theo dõi (không đổi)")
            except Exception as e:
                if self.on_error:
                    self.on_error(str(e))
                if self.on_status:
                    self.on_status("Lỗi kết nối (thử lại...)")
            for _ in range(max(1, int(self.poll_seconds * 5))):
                if not self._running or stop_flag:
                    break
                time.sleep(0.2)
        if self.on_status:
            self.on_status("Đã dừng")

# -------------------- MONITOR --------------------

def monitor_loop():
    global last_balance_fetch_ts, last_msg_ts, stop_flag
    while not stop_flag:
        now = time.time()
        if now - last_balance_fetch_ts >= BALANCE_POLL_INTERVAL * 2:
            last_balance_fetch_ts = now
            try:
                fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
            except Exception as e:
                log_debug(f"monitor fetch err: {e}")
        
        if now - last_msg_ts > 8:
            log_debug("No ws msg >8s, send enter_game")
            try:
                safe_send_enter_game(_ws.get("ws"))
            except Exception as e:
                log_debug(f"monitor send err: {e}")
        if now - last_msg_ts > 20:
            log_debug("No ws msg >20s, force reconnect")
            try:
                wsobj = _ws.get("ws")
                if wsobj:
                    try:
                        wsobj.close()
                    except Exception:
                        pass
            except Exception:
                pass
        time.sleep(0.6)

# -------------------- UI (RICH) - GOLD/YELLOW THEME --------------------

def _spinner_char() -> str:
    return _spinner[int(time.time() * 4) % len(_spinner)]

def _gold_border_style() -> str:
    idx = int(time.time() * 2) % 2
    return MAIN_COLOR if idx == 0 else ACCENT_COLOR

def make_layout() -> Layout:
    """Tạo bố cục màn hình chính theo phong cách của CB1fix.py"""
    layout = Layout(name="root")

    # Chia bố cục chính thành 3 hàng: Header, Content, Footer (Bet History)
    layout.split_column(
        Layout(name="header", size=4), 
        Layout(name="content", ratio=4),
        Layout(name="footer", ratio=2) 
    )

    # Chia Content thành 2 cột: Left (Rooms Table) và Right (Mid Panel & Stat)
    layout["content"].split_row(
        Layout(name="content.left", ratio=3), # Rooms Table (RỘNG HƠN)
        Layout(name="content.right", ratio=2) # Hẹp hơn
    )

    # Chia Content Right thành 2 hàng: Mid Panel và Stat Placeholder
    layout["content.right"].split_column(
        Layout(name="content.right.mid", size=9), # Kích thước cố định cho Mid Panel
        Layout(name="content.right.stat_placeholder", ratio=1) # Phần thống kê
    )
    return layout

def build_header(border_color: Optional[str] = None) -> Panel:
    tbl = Table.grid(expand=True, padding=(0, 1))
    tbl.add_column(ratio=2)
    tbl.add_column(ratio=1)

    # Dòng 1: Tiêu đề và Thời gian
    left_title = Text.assemble(
        (f"[{MAIN_COLOR} bold]👑 GODMODE V3.0 [/]"), 
        (f"[{ACCENT_COLOR}] - {SELECTION_MODES.get(settings.get('algo', ''), settings.get('algo'))}[/]")
    )
    right_time = Text(f"[{TEXT_COLOR}]{datetime.now(tz).strftime('%Y/%m/%d %H:%M:%S')}  •  {_spinner_char()}[/]", style="dim")
    tbl.add_row(Align.left(left_title), Align.right(right_time))

    # Dòng 2: Số dư và Cấu hình
    b = f"{current_build:,.4f}" if isinstance(current_build, (int, float)) else (str(current_build) if current_build is not None else "-")
    u = f"{current_usdt:,.4f}" if isinstance(current_usdt, (int, float)) else (str(current_usdt) if current_usdt is not None else "-")

    pnl_val = cumulative_profit if cumulative_profit is not None else 0.0
    pnl_str = f"{pnl_val:+,.4f}"
    pnl_style = SUCCESS_COLOR if pnl_val > 0 else (FAILURE_COLOR if pnl_val < 0 else PENDING_COLOR)
    
    pnl_text = Text.assemble(
        (f"[{TEXT_COLOR}]Lãi/lỗ tích lũy: [/{TEXT_COLOR}]",), 
        (f"[{pnl_style} bold]{pnl_str}[/]",)
    )
    
    targets = []
    if stop_when_profit_reached and profit_target is not None:
         targets.append(f"[{SUCCESS_COLOR}]🏆 TP@{profit_target:,.2f}[/]")
    if stop_when_loss_reached and stop_loss_target is not None:
         targets.append(f"[{FAILURE_COLOR}]🛡️ SL@{stop_loss_target:,.2f}[/]")
    
    target_text = Text.from_markup(" | ".join(targets))

    balance_text = Text.assemble(
         (f"[{TEXT_COLOR}]BUILD: [/{TEXT_COLOR}]",), (f"[{MAIN_COLOR} bold]{b} | [/]",), 
         (f"[{TEXT_COLOR}]USDT: [/{TEXT_COLOR}]",), (f"[{PENDING_COLOR}]{u}[/]")
    )
    
    right_info = Table.grid(padding=(0, 0))
    right_info.add_row(Align.right(pnl_text))
    if targets:
        right_info.add_row(Align.right(target_text))
    
    tbl.add_row(
        Align.left(balance_text), 
        Align.right(right_info)
    )

    panel = Panel(
        tbl, 
        box=box.HEAVY_HEAD, 
        padding=(0,1), 
        border_style=(border_color or _gold_border_style())
    )
    return panel

def build_rooms_table(border_color: Optional[str] = None) -> Panel:
    t = Table(box=box.MINIMAL_DOUBLE_HEAD, expand=True, title=Text("📊 DỮ LIỆU PHÒNG VÀNG", style=f"bold {MAIN_COLOR}"))
    t.add_column("[#ffffff]ID[/]", justify="center", width=3, style=PENDING_COLOR)
    t.add_column("[#ffffff]Phòng[/]", width=18, style=TEXT_COLOR)
    t.add_column("[#ffffff]Players[/]", justify="right", style=ACCENT_COLOR)
    t.add_column("[#ffffff]Total Bet[/]", justify="right", style=MAIN_COLOR, min_width=12)
    t.add_column("[#ffffff]Status[/]", justify="center", style=TEXT_COLOR)
    
    for r in ROOM_ORDER:
        st = room_state.get(r, {})
        
        players = st.get("players", 0)
        bet_val = st.get('bet', 0) or 0
        status = ""
        row_style = ""
        
        bet_fmt = f"{bet_val:,.4f}" 
        
        is_last_kill = False
        try:
            if killed_room is not None and int(r) == int(killed_room):
                status = f"[{FAILURE_COLOR}]☠ KILL[/]"
                row_style = FAILURE_COLOR
                is_last_kill = True
        except Exception:
            pass
            
        try:
            if predicted_room is not None and int(r) == int(predicted_room):
                status = (status + f" [dim]|[/] [{SUCCESS_COLOR}]✓ DỰ ĐOÁN[/]") if status else f"[{SUCCESS_COLOR}]✓ DỰ ĐOÁN[/]"
                if not is_last_kill:
                    row_style = SUCCESS_COLOR 
        except Exception:
            pass
            
        t.add_row(
            str(r), 
            ROOM_NAMES.get(r, f"Phòng {r}"), 
            str(players), 
            bet_fmt, 
            status, 
            style=row_style
        )
        
    return Panel(t, title_align="left", border_style=(border_color or _gold_border_style()), padding=(0, 1))

def build_mid(border_color: Optional[str] = None) -> Panel:
    global analysis_start_ts, analysis_blur
    
    current_border = border_color or _gold_border_style()
    
    if ui_state == "ANALYZING":
        lines = []
        lines.append(f"[{PENDING_COLOR} bold]ĐANG PHÂN TÍCH PHÒNG CHIẾN THẦN {_spinner_char()}[/]")
        
        cd_val = int(count_down) if count_down is not None else None
        
        if cd_val is not None:
            lines.append(f"[{TEXT_COLOR}]Đếm ngược tới kết quả: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{cd_val}s[/]")
        else:
            lines.append(f"[{ACCENT_COLOR}]Chưa nhận được dữ liệu đếm ngược...[/]")

        if analysis_blur:
            bar_len = 36
            blocks = []
            tbase = int(time.time() * 5)
            for i in range(bar_len):
                val = (tbase + i) % 7
                ch = "█" if val in (0, 1, 2, 3) else "░"
                color = MAIN_COLOR if val % 2 == 0 else ACCENT_COLOR
                blocks.append(f"[{color}]{ch}[/{color}]")
            lines.append("".join(blocks))
            lines.append("")
            lines.append(f"[{MAIN_COLOR} bold]AI ĐANG TÍNH TOÁN 10S CUỐI VÀO BUID[/]")
        else:
            lines.append(f"[{TEXT_COLOR}]Waiting for 10s window...[/]")
            
        lines.append(f"[{TEXT_COLOR}]Phòng sát thủ ván trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        
        txt = "\n".join(lines)
        return Panel(
            Align.center(Text.from_markup(txt), vertical="middle"), 
            title=Text("✨ PHÂN TÍCH GODMODE", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=9,
            padding=(0, 1)
        )

    elif ui_state == "PREDICTED":
        name = ROOM_NAMES.get(predicted_room, f"Phòng {predicted_room}") if predicted_room else '-'
        
        last_bet_amt_display = f"{current_bet:,.4f}" if isinstance(current_bet, (int, float)) and current_bet is not None else '-'
        
        lines = []
        lines.append(f"[{ACCENT_COLOR} bold]👑 AI CHỌN: [/][{SUCCESS_COLOR} bold]{name}[/] - KẾT QUẢ DỰ ĐOÁN")
        lines.append(f"[{TEXT_COLOR}]Số đặt: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{last_bet_amt_display} BUILD[/]")
        lines.append(f"[{TEXT_COLOR}]Phòng sát thủ ván trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        lines.append(f"[{TEXT_COLOR}]Chuỗi: [/{TEXT_COLOR}][{SUCCESS_COLOR}]W={win_streak}[/] | [{FAILURE_COLOR}]L={lose_streak}[/]")
        
        cd_val = int(count_down) if count_down is not None else None
        if cd_val is not None:
            lines.append(f"[{TEXT_COLOR}]Đếm ngược tới kết quả: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{cd_val}s[/]")
        
        lines.append(f"[{PENDING_COLOR}]Đang chờ sát thủ ra tay {_spinner_char()}[/]")
        
        txt = "\n".join(lines)
        
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("🎯 DỰ ĐOÁN CHIẾN THẦN", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=9,
            padding=(0, 1)
        )

    elif ui_state == "RESULT":
        k = ROOM_NAMES.get(killed_room, "-") if killed_room else "-"
        
        border = current_border
        last_result_rec = bet_history[-1] if bet_history else None
        last_result = last_result_rec.get('result') if last_result_rec else None
        
        if last_result == 'Thắng':
            border = SUCCESS_COLOR
            result_line = f"[{SUCCESS_COLOR} bold]✅ THẮNG CƯỢC! Lợi nhuận tích lũy: {cumulative_profit:+.4f} BUILD[/]"
        elif last_result == 'Thua':
            border = FAILURE_COLOR
            result_line = f"[{FAILURE_COLOR} bold]❌ THUA CƯỢC! Lỗ tích lũy: {cumulative_profit:+.4f} BUILD[/]"
        else:
            result_line = f"[{PENDING_COLOR} bold]Kết quả chưa xác định (Ván {issue_id}).[/]"

        lines = []
        lines.append(f"[{FAILURE_COLOR} bold]⚔️ SÁT THỦ ĐÃ VÀO: [/][{PENDING_COLOR} bold]{k}[/]")
        lines.append(result_line)
        lines.append(f"[{TEXT_COLOR}]Chuỗi hiện tại: [/{TEXT_COLOR}][{SUCCESS_COLOR}]W={win_streak}[/] | [{FAILURE_COLOR}]L={lose_streak}[/]")
        lines.append(f"[{TEXT_COLOR}]Cược tiếp theo: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{current_bet:,.4f} BUILD[/]")
        lines.append(f"[{TEXT_COLOR}]Ván chơi tiếp theo: [/{TEXT_COLOR}][{PENDING_COLOR} bold]{(issue_id or 0) + 1}[/]")
        
        txt = "\n".join(lines)
        
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("🔔 KẾT QUẢ VÁN", style=f"bold {MAIN_COLOR}"), 
            border_style=border, 
            height=9,
            padding=(0, 1)
        )
    
    else:
        lines = []
        if _skip_rounds_remaining > 0:
             lines.append(f"[{ACCENT_COLOR} bold]⏸️ ĐANG NGHỈ SAU THUA ({_skip_rounds_remaining} ván)[/]")
        elif skip_next_round_flag:
             lines.append(f"[{ACCENT_COLOR} bold]⏸️ ĐANG NGHỈ CHỐNG SOI (1 ván)[/]")
        else:
             lines.append(f"[{PENDING_COLOR} bold]--- HỆ THỐNG GODMODE ĐANG KHỞI ĐỘNG ---[/]")
             
        lines.append(f"[{TEXT_COLOR}]Chờ ván mới...[/]")
        lines.append(f"[{TEXT_COLOR}]Phòng sát thủ ván trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        lines.append(f"[{TEXT_COLOR}]AI chọn: [/{TEXT_COLOR}][{PENDING_COLOR}]{ROOM_NAMES.get(predicted_room, '-') if predicted_room else '-'}[/]")
        profit_style = SUCCESS_COLOR if cumulative_profit >= 0 else FAILURE_COLOR
        lines.append(f"[{TEXT_COLOR}]Lãi/lỗ tích lũy: [/{TEXT_COLOR}][{profit_style} bold]{cumulative_profit:+.4f} BUILD[/]")
        
        txt = "\n".join(lines)
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("⚙️ TRẠNG THÁI HỆ THỐNG", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=9,
            padding=(0, 1)
        )

def build_bet_table(border_color: Optional[str] = None) -> Panel:
    t = Table(title=Text("📜 LỊCH SỬ CƯỢC (10 VÁN GODMODE)", style=f"bold {MAIN_COLOR}"), box=box.HEAVY_EDGE, expand=True)
    t.add_column("[#ffffff]Ván[/]", justify="center", no_wrap=True, style=PENDING_COLOR)
    t.add_column("[#ffffff]Phòng Đặt[/]", justify="center", no_wrap=True, style=TEXT_COLOR)
    t.add_column("[#ffffff]Tiền Đặt[/]", justify="right", no_wrap=True, style=MAIN_COLOR)
    t.add_column("[#ffffff]K Q[/]", justify="center", no_wrap=True)
    t.add_column("[#ffffff]Phòng KILL[/]", justify="center", no_wrap=True, style=ACCENT_COLOR)
    t.add_column("[#ffffff]Thuật toán[/]", no_wrap=True, style="dim")
    
    last10 = list(bet_history)[-10:]
    
    for b in reversed(last10):
        issue = str(b.get('issue') or '-')
        placed_room = str(b.get('room') or '-')
        amt = b.get('amount') or 0
        
        amt_fmt = f"{float(amt):,.4f}"
             
        res = str(b.get('result') or '-')
        algo = str(b.get('algo') or '-')
        
        killed_id = b.get("killed_room_id")
        killed_room_display = "-"
        kr_style = ACCENT_COLOR
        
        if killed_id is not None:
             killed_room_display = ROOM_NAMES.get(killed_id, str(killed_id))
             if placed_room.isdigit() and int(placed_room) == killed_id:
                  kr_style = FAILURE_COLOR
             else:
                  kr_style = SUCCESS_COLOR

        if b.get('issue') == issue_id and killed_room is not None and killed_id is None:
             killed_room_display = ROOM_NAMES.get(killed_room, str(killed_room))
             if placed_room.isdigit() and int(placed_room) == killed_room:
                 kr_style = FAILURE_COLOR
             else:
                 kr_style = SUCCESS_COLOR
        
        if res.lower().startswith('thắng') or res.lower().startswith('win'):
            res_text = Text(res, style=SUCCESS_COLOR)
        elif res.lower().startswith('thua') or res.lower().startswith('lose'):
            res_text = Text(res, style=FAILURE_COLOR)
        else:
            res_text = Text(res, style=PENDING_COLOR)
            
        t.add_row(
            issue, 
            placed_room, 
            amt_fmt, 
            res_text, 
            Text(killed_room_display, style=kr_style),
            algo
        )
        
    return Panel(t, border_style=(border_color or _gold_border_style()), padding=(0, 1))

def update_layout(layout: Layout) -> None:
    """
    Cập nhật nội dung cho bố cục, BAO GỒM THỐNG KÊ MỚI: Tổng W/L và Tỷ lệ Win.
    """
    global max_lose_streak
    
    total_wins = sum(1 for b in bet_history if b.get('result') == 'Thắng')
    total_losses = sum(1 for b in bet_history if b.get('result') == 'Thua')
    total_settled_rounds = total_wins + total_losses
    win_rate = (total_wins / total_settled_rounds) * 100 if total_settled_rounds > 0 else 0.0
    
    header_panel = build_header(border_color=_gold_border_style())
    layout["header"].update(header_panel)
    
    rooms_panel = build_rooms_table(border_color=_gold_border_style())
    layout["content.left"].update(rooms_panel)

    mid_panel = build_mid(border_color=_gold_border_style())
    layout["content.right.mid"].update(mid_panel)
    
    bet_history_panel = build_bet_table(border_color=_gold_border_style())
    layout["footer"].update(bet_history_panel)
    
    pnl_val = cumulative_profit if cumulative_profit is not None else 0.0
    pnl_style = SUCCESS_COLOR if pnl_val > 0 else (FAILURE_COLOR if pnl_val < 0 else PENDING_COLOR)
    
    stat_content = Table.grid(padding=(0,1))
    stat_content.add_column()
    
    current_build_fmt = f"{current_build:,.4f}" if isinstance(current_build, (int, float)) else '-'
    
    stat_lines = [
        f"[{TEXT_COLOR}]Số dư BUILD: [/{TEXT_COLOR}][{TEXT_COLOR} bold]{current_build_fmt} BUILD[/]",
        f"[{TEXT_COLOR}]Phiên hiện tại: [/{TEXT_COLOR}][{PENDING_COLOR}]{issue_id or '-'}[/]",
        f"[{TEXT_COLOR}]Tổng ván chơi: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{round_index}[/]",
        f"[{TEXT_COLOR}]Lãi/Lỗ Tích Lũy: [/{TEXT_COLOR}][{pnl_style} bold]{pnl_val:+.4f} BUILD[/]",
        f"[{TEXT_COLOR}]Tổng W/L: [/{TEXT_COLOR}][{SUCCESS_COLOR}]{total_wins}[/]/[{FAILURE_COLOR}]{total_losses}[/]",
        f"[{TEXT_COLOR}]Tỷ lệ Win: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{win_rate:.2f}%[/]",
        f"[{TEXT_COLOR}]MAX W/L: [/{TEXT_COLOR}][{SUCCESS_COLOR}]{max_win_streak}[/]/[{FAILURE_COLOR}]{max_lose_streak}[/]",
    ]
    stat_content.add_row(Align.left(Text.from_markup("\n".join(stat_lines))))

    layout["content.right.stat_placeholder"].update(Panel(
        stat_content,
        title=Text("📈 THỐNG KÊ HOẠT ĐỘNG", style=f"bold {ACCENT_COLOR}"),
        height=9, 
        border_style=_gold_border_style(),
        padding=(0, 1)
    ))

# -------------------- SETTINGS & START --------------------

def prompt_settings():
    global base_bet, multiplier, run_mode, bet_rounds_before_skip, current_bet, pause_after_losses, profit_target, stop_when_profit_reached, stop_loss_target, stop_when_loss_reached, settings
    global SELECTION_CONFIG
    
    console.print(Rule(f"[bold {MAIN_COLOR}]CẤU HÌNH CHIẾN THẦN[/]",style=ACCENT_COLOR))
    base = safe_input(f"[{TEXT_COLOR}]Số BUILD đặt mỗi ván (>=1.0): [/{TEXT_COLOR}]", default="1.0")
    try:
        base_bet = float(base)
    except Exception:
        base_bet = 1.0
    current_bet = base_bet

    console.print(f"\n[{TEXT_COLOR} bold]Chọn Chiến lược Quản lý Cược:[/{TEXT_COLOR}]")
    console.print(f"[{ACCENT_COLOR}]1) MARTINGALE (Mặc định):[/{ACCENT_COLOR}] Nhân tiền khi thua (hạn chế chuỗi thua).")
    console.print(f"[{ACCENT_COLOR}]2) ANTI-MARTINGALE:[/{ACCENT_COLOR}] Tăng nhẹ tiền khi thắng (tối đa hóa lợi nhuận).")
    strategy_choice = safe_input(f"[{TEXT_COLOR}]Chọn (1/2): [/{TEXT_COLOR}]", default="1")
    if str(strategy_choice).strip() == "2":
        SELECTION_CONFIG["bet_management_strategy"] = "ANTI-MARTINGALE"
    else:
        SELECTION_CONFIG["bet_management_strategy"] = "MARTINGALE"
    
    m = safe_input(f"[{TEXT_COLOR}]Nhập 1 số nhân sau khi thua (ổn định thì 2): [/{TEXT_COLOR}]", default="2.0")
    try:
        multiplier = float(m)
    except Exception:
        multiplier = 2.0
    
    settings["algo"] = "GODMODE"
    console.print(f"\n[{ACCENT_COLOR} bold]✅ Thuật toán: CHIẾN THẦN PROMAX - HÀO QUANG CỦA THẦN[/]")

    s = safe_input(f"[{TEXT_COLOR}]Chống soi: sau bao nhiêu ván đặt thì nghỉ 1 ván: [/{TEXT_COLOR}]", default="0")
    try:
        bet_rounds_before_skip = int(s)
    except Exception:
        bet_rounds_before_skip = 0
    
    pl = safe_input(f"[{TEXT_COLOR}]Nếu thua thì nghỉ bao nhiêu tay trước khi cược lại (ví dụ 2): [/{TEXT_COLOR}]", default="0")
    try:
        pause_after_losses = int(pl)
    except Exception:
        pause_after_losses = 0
    
    pt = safe_input(f"[{TEXT_COLOR}]lãi bao nhiêu thì chốt (BUILD, không dùng enter): [/{TEXT_COLOR}]", default="")
    try:
        if pt and pt.strip() != "":
            profit_target = float(pt)
            stop_when_profit_reached = True
        else:
            profit_target = None
            stop_when_profit_reached = False
    except Exception:
        profit_target = None
        stop_when_profit_reached = False
        
    sl = safe_input(f"[{TEXT_COLOR}]lỗ bao nhiêu thì chốt (BUILD, không dùng enter): [/{TEXT_COLOR}]", default="")
    try:
        if sl and sl.strip() != "":
            stop_loss_target = float(sl)
            stop_when_loss_reached = True
        else:
            stop_loss_target = None
            stop_when_loss_reached = False
    except Exception:
        stop_loss_target = None
        stop_when_loss_reached = False

    runm = safe_input(f"[{MAIN_COLOR} bold]💯bạn đã sẵn sàng hãy nhấn enter để bắt đầu💯: [/{MAIN_COLOR}]", default="AUTO")
    run_mode = str(runm).upper()

def start_threads():
    threading.Thread(target=start_ws, daemon=True).start()
    threading.Thread(target=monitor_loop, daemon=True).start()

def parse_login():
    global USER_ID, SECRET_KEY
    console.print(Rule(f"[bold {MAIN_COLOR}]ĐĂNG NHẬP[/]",style=ACCENT_COLOR))
    link = safe_input(f"[{TEXT_COLOR}]Dán link trò chơi (từ xworld.info) tại đây (ví dụ chứa userId & secretKey) > [/{TEXT_COLOR}]", default=None)
    if not link:
        console.print(f"[{FAILURE_COLOR}]Không nhập link. Thoát.[/]")
        sys.exit(1)
    try:
        parsed = urlparse(link)
        params = parse_qs(parsed.query)
        
        temp_uid = params.get('userId', [None])[0] or params.get('uid', [None])[0]
        temp_secret = params.get('secretKey', [None])[0] or params.get('secret', [None])[0]
        
        if temp_uid:
            USER_ID = int(temp_uid)
        SECRET_KEY = temp_secret
        
        if USER_ID is None or SECRET_KEY is None:
             raise ValueError("Missing USER_ID or SECRET_KEY")
             
        console.print(f"[{SUCCESS_COLOR}]✅ Đã đọc: userId={USER_ID}[/]")
    except Exception as e:
        console.print(f"[{FAILURE_COLOR}]Link không hợp lệ. Vui lòng kiểm tra lại link đã dán có chứa userId và secretKey. Thoát.[/]")
        log_debug(f"parse_login err: {e}")
        sys.exit(1)

def main():
    parse_login()
    console.print(f"[{MAIN_COLOR} bold]Loading...[/]")
    prompt_settings()
    console.print(f"[{SUCCESS_COLOR} bold]Bắt đầu kết nối dữ liệu (GODMODE)...[/]")

    def on_balance_changed(bal, delta, info):
        color = SUCCESS_COLOR if delta > 0 else (FAILURE_COLOR if delta < 0 else PENDING_COLOR)
        console.print(f"[{SUCCESS_COLOR}]⤴️ cập nhật số dư: [/{SUCCESS_COLOR}][{MAIN_COLOR}]{bal:,.4f}[/] (Δ [{color}]{delta:+.4f}[/]) — [{PENDING_COLOR}]{info.get('ts')}[/]")

    def on_error(msg):
        console.print(f"[{FAILURE_COLOR}]Balance poll lỗi: {msg}[/]")

    poller = BalancePoller(USER_ID, SECRET_KEY, poll_seconds=max(1, int(BALANCE_POLL_INTERVAL)), on_balance=on_balance_changed, on_error=on_error, on_status=None)
    poller.start()
    start_threads()

    main_layout = make_layout()

    with Live(
        main_layout, 
        refresh_per_second=8, 
        console=console, 
        screen=True
    ) as live:
        try:
            while not stop_flag:
                update_layout(main_layout)
                time.sleep(0.12)
            console.print(f"[{MAIN_COLOR} bold]Tool đã dừng theo yêu cầu hoặc đạt mục tiêu.[/]")
        except KeyboardInterrupt:
            console.print(f"[{ACCENT_COLOR}]Thoát bằng người dùng.[/]")
            poller.stop()
            sys.exit(0)
        except Exception as e:
            console.print(f"[{FAILURE_COLOR}]Lỗi nghiêm trọng trong vòng lặp chính: {e}[/]")
            log_debug(f"Main loop error: {e}")
            poller.stop()

if __name__ == "__main__":
    main()