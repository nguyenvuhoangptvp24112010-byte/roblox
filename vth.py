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
from typing import Any, Dict, Tuple, Optional, List
from statistics import pstdev, mean
import os
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

console = Console()
tz = pytz.timezone("Asia/Ho_Chi_Minh")
logger = logging.getLogger("escape_vip_ai_pro")
logger.setLevel(logging.INFO)
logger.addHandler(logging.FileHandler("escape_vip_ai_pro.log", encoding="utf-8"))
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

def room_label(room_id: int, include_id: bool = True) -> str:
    try:
        rid = int(room_id)
    except Exception:
        rid = room_id
    name = ROOM_NAMES.get(rid, f"Phòng {rid}")
    return f"PHÒNG_{rid} — {name}" if include_id else name

ROOM_ORDER = [1, 2, 3, 4, 5, 6, 7, 8]
USER_ID: Optional[int] = None
SECRET_KEY: Optional[str] = None
issue_id: Optional[int] = None
issue_start_ts: Optional[float] = None
count_down: Optional[int] = None
killed_room: Optional[int] = None
round_index: int = 0
_skip_active_issue: Optional[int] = None

room_state: Dict[int, Dict[str, Any]] = {r: {"players": 0, "bet": 0} for r in ROOM_ORDER}
room_stats: Dict[int, Dict[str, Any]] = {r: {"kills": 0, "survives": 0, "last_kill_round": None, "last_players": 0, "last_bet": 0} for r in ROOM_ORDER}

predicted_room: Optional[int] = None
last_killed_room: Optional[int] = None
prediction_locked: bool = False
current_build: Optional[float] = None
current_usdt: Optional[float] = None
current_world: Optional[float] = None
last_balance_ts: Optional[float] = None
last_balance_val: Optional[float] = None
starting_balance: Optional[float] = None
cumulative_profit: float = 0.0
total_wins: int = 0
total_losses: int = 0
win_rate: float = 0.0
win_streak: int = 0
lose_streak: int = 0
max_win_streak: int = 0
max_lose_streak: int = 0
base_bet: float = 1.0
multiplier: float = 2.0
current_bet: Optional[float] = None
run_mode: str = "AUTO"
betting_mode: str = "DEMO"
bet_rounds_before_skip: int = 0
_rounds_placed_since_skip: int = 0
skip_next_round_flag: bool = False
bet_history: deque = deque(maxlen=500)
bet_sent_for_issue: set = set()
pause_after_losses: int = 0
_skip_rounds_remaining: int = 0
profit_target: Optional[float] = None
stop_when_profit_reached: bool = False
stop_loss_target: Optional[float] = None
stop_when_loss_reached: bool = False
stop_flag: bool = False
ui_state: str = "IDLE"
analysis_start_ts: Optional[float] = None
analysis_blur: bool = False
last_msg_ts: float = time.time()
last_balance_fetch_ts: float = 0.0
BALANCE_POLL_INTERVAL: float = 4.0
_ws: Dict[str, Any] = {"ws": None}
SELECTION_CONFIG = {
    "max_bet_allowed": float("inf"),
    "max_players_allowed": 9999,
    "avoid_last_kill": True,
}

ADVANCED_ALGORITHMS = {
    "QUANTUM": "Quantum Probability Matrix",
    "PATTERN": "Advanced Pattern Master", 
    "FUSION": "Fusion AI System",
    "PREDATOR": "Predator Instinct AI"
}

settings = {"algo": "FUSION"}
HIST_K = 20
room_hist = {r: deque(maxlen=HIST_K) for r in ROOM_ORDER}
room_trends = {r: {"momentum": 0, "volatility": 0, "stability": 0} for r in ROOM_ORDER}

_spinner = ["📦", "🪑", "👔", "💬", "🎥", "🏢", "💰", "👥"]
_num_re = re.compile(r"-?\d+[\d,]*\.?\d*")
RAINBOW_COLORS = ["red", "orange1", "yellow1", "green", "cyan", "blue", "magenta"]
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
def calculate_room_potential(room_id: int) -> Dict[str, float]:
    """Phân tích tiềm năng toàn diện của phòng"""
    analysis = {}
    current_data = room_state[room_id]
    players = current_data.get('players', 0)
    bet = current_data.get('bet', 0)
    bet_per_player = bet / max(players, 1)
    stats = room_stats[room_id]
    kills = stats.get("kills", 0)
    survives = stats.get("survives", 0)
    total_games = kills + survives
    survival_rate = survives / max(total_games, 1) if total_games > 0 else 0.5
    data_confidence = min(1.0, total_games / 12.0)
    weighted_survival = 0.5 * (1 - data_confidence) + survival_rate * data_confidence
    
    analysis['survival_rate'] = weighted_survival
    trend_score = analyze_trend_pattern(room_id)
    analysis['trend'] = trend_score
    crowd_analysis = analyze_crowd_behavior(room_id)
    analysis['crowd'] = crowd_analysis
    risk_score = calculate_risk_factor(room_id)
    analysis['risk'] = risk_score
    total_score = (
        weighted_survival * 0.35 +
        trend_score * 0.25 +
        crowd_analysis * 0.25 +
        (1 - risk_score) * 0.15
    )
    
    analysis['total_score'] = max(0.1, min(0.95, total_score))
    analysis['confidence'] = data_confidence
    
    return analysis

def analyze_trend_pattern(room_id: int) -> float:
    hist = list(room_hist[room_id])
    if len(hist) < 3:
        return 0.5
    
    players = [h['players'] for h in hist]
    bets = [h['bet'] for h in hist]
    momentum = calculate_momentum(players, bets)
    cycle_strength = analyze_cycle_strength(players)
    breakout_potential = detect_breakout(players, bets)
    mean_reversion = calculate_mean_reversion(players)
    trend_score = 0.5
    trend_score += momentum * 0.3
    trend_score += cycle_strength * 0.2
    trend_score += breakout_potential * 0.25
    trend_score += mean_reversion * 0.25
    
    return max(0.1, min(0.9, trend_score))

def calculate_momentum(players: List[int], bets: List[float]) -> float:
    if len(players) < 3:
        return 0.0
    short_players = players[-3:] if len(players) >= 3 else players
    short_bets = bets[-3:] if len(bets) >= 3 else bets
    
    player_momentum = (short_players[-1] - short_players[0]) / max(mean(short_players), 1)
    bet_momentum = (short_bets[-1] - short_bets[0]) / max(mean(short_bets), 1)
    if len(players) >= 5:
        mid_players = players[-5:]
        mid_bets = bets[-5:]
        player_mid_momentum = (mid_players[-1] - mid_players[0]) / max(mean(mid_players), 1)
        bet_mid_momentum = (mid_bets[-1] - mid_bets[0]) / max(mean(mid_bets), 1)
    else:
        player_mid_momentum = player_momentum
        bet_mid_momentum = bet_momentum
    total_momentum = (
        player_momentum * 0.4 +
        bet_momentum * 0.3 +
        player_mid_momentum * 0.2 +
        bet_mid_momentum * 0.1
    )
    
    return max(-0.4, min(0.4, total_momentum))

def analyze_cycle_strength(players: List[int]) -> float:
    if len(players) < 4:
        return 0.0
    lows = []
    highs = []
    
    for i in range(1, len(players)-1):
        if players[i] < players[i-1] and players[i] < players[i+1]:
            lows.append(players[i])
        elif players[i] > players[i-1] and players[i] > players[i+1]:
            highs.append(players[i])
    if len(lows) >= 2 and len(highs) >= 2:
        low_stability = 1.0 - (pstdev(lows) / max(mean(lows), 1))
        high_stability = 1.0 - (pstdev(highs) / max(mean(highs), 1))
        cycle_stability = (low_stability + high_stability) / 2.0
    else:
        cycle_stability = 0.3
    
    return max(0.0, min(1.0, cycle_stability))

def detect_breakout(players: List[int], bets: List[float]) -> float:
    """Phát hiện breakout tiềm năng"""
    if len(players) < 4:
        return 0.0
    current_players = players[-1]
    avg_players = mean(players[:-1]) if len(players) > 1 else current_players
    
    current_bet = bets[-1]
    avg_bet = mean(bets[:-1]) if len(bets) > 1 else current_bet
    player_breakout = current_players / max(avg_players, 1)
    bet_breakout = current_bet / max(avg_bet, 1)
    if player_breakout > 1.2 and bet_breakout > 1.1:
        breakout_score = 0.8
    elif player_breakout > 1.1 and bet_breakout > 1.0:
        breakout_score = 0.6
    elif player_breakout < 0.8 and bet_breakout < 0.9:
        breakout_score = 0.3
    else:
        breakout_score = 0.5
    
    return breakout_score

def calculate_mean_reversion(players: List[int]) -> float:
    if len(players) < 4:
        return 0.5
    
    current = players[-1]
    historical_avg = mean(players[:-1])
    
    if historical_avg == 0:
        return 0.5
    
    deviation = abs(current - historical_avg) / historical_avg
    if deviation > 0.5:
        mean_reversion = 0.8
    elif deviation > 0.3:
        mean_reversion = 0.6
    elif deviation > 0.1:
        mean_reversion = 0.4
    else:
        mean_reversion = 0.2
    
    return mean_reversion

def analyze_crowd_behavior(room_id: int) -> float:
    current_data = room_state[room_id]
    players = current_data.get('players', 0)
    bet = current_data.get('bet', 0)
    all_players = [room_state[r]['players'] for r in ROOM_ORDER]
    all_bets = [room_state[r]['bet'] for r in ROOM_ORDER]
    
    total_players = sum(all_players)
    total_bets = sum(all_bets)
    
    if total_players == 0 or total_bets == 0:
        return 0.5
    player_share = players / total_players
    bet_share = bet / total_bets
    smi = bet_share - player_share
    if player_share < 0.05:
        crowd_effect = 0.7 
    elif player_share > 0.25:
        crowd_effect = 0.3
    else:
        crowd_effect = 0.5
    if smi > 0.1:
        crowd_score = 0.6 + min(0.3, smi * 2)
    elif smi < -0.1:
        crowd_score = 0.4 + max(-0.2, smi * 2)
    else:
        crowd_score = 0.5
    final_score = crowd_score * 0.7 + crowd_effect * 0.3
    
    return max(0.1, min(0.9, final_score))

def calculate_risk_factor(room_id: int) -> float:
    risk_factors = []
    if last_killed_room == room_id:
        risk_factors.append(0.7)
    stats = room_stats[room_id]
    kills = stats.get("kills", 0)
    survives = stats.get("survives", 0)
    total = kills + survives
    
    if total > 0:
        kill_rate = kills / total
        if kill_rate > 0.7:
            risk_factors.append(0.6)
        elif kill_rate > 0.5:
            risk_factors.append(0.4)
    players = room_state[room_id].get('players', 0)
    if players < 2:
        risk_factors.append(0.8)
    elif players > 50:
        risk_factors.append(0.4)
    hist = list(room_hist[room_id])
    if len(hist) >= 3:
        player_vals = [h['players'] for h in hist]
        volatility = pstdev(player_vals) / max(mean(player_vals), 1)
        if volatility > 0.6:
            risk_factors.append(0.5)
        elif volatility > 0.3:
            risk_factors.append(0.3)
    if count_down is not None and count_down <= 10:
        risk_factors.append(0.3)
    
    if not risk_factors:
        return 0.3
    
    return min(0.9, mean(risk_factors))

def choose_room_quantum() -> Tuple[int, str, float]:
    scores = {}
    analyses = {}
    
    for room_id in ROOM_ORDER:
        analysis = calculate_room_potential(room_id)
        scores[room_id] = analysis['total_score']
        analyses[room_id] = analysis
    
    if not scores:
        return random.choice(ROOM_ORDER), "QUANTUM-FALLBACK", 0.5
    best_room, best_score = max(scores.items(), key=lambda x: x[1])
    sorted_scores = sorted(scores.values(), reverse=True)
    if len(sorted_scores) > 1:
        score_gap = sorted_scores[0] - sorted_scores[1]
        base_confidence = best_score * 0.7
        gap_bonus = min(0.25, score_gap * 3.0)
        analysis_bonus = analyses[best_room]['confidence'] * 0.1
        
        confidence = base_confidence + gap_bonus + analysis_bonus
    else:
        confidence = best_score * 0.7
    
    return best_room, "QUANTUM-PRO", min(0.95, confidence)

def choose_room_pattern() -> Tuple[int, str, float]:
    pattern_scores = {}
    for room_id in ROOM_ORDER:
        trend_analysis = analyze_trend_pattern(room_id)
        crowd_analysis = analyze_crowd_behavior(room_id)
        risk_analysis = 1.0 - calculate_risk_factor(room_id)
        total_score = (
            trend_analysis * 0.4 +
            crowd_analysis * 0.35 +
            risk_analysis * 0.25
        )
        
        pattern_scores[room_id] = total_score
    
    if not pattern_scores:
        return random.choice(ROOM_ORDER), "PATTERN-FALLBACK", 0.5
    
    best_room, best_score = max(pattern_scores.items(), key=lambda x: x[1])
    avg_score = mean(pattern_scores.values())
    score_ratio = best_score / max(avg_score, 0.1)
    
    if score_ratio > 1.3:
        confidence = min(0.9, best_score * 0.8 + 0.2)
    elif score_ratio > 1.1:
        confidence = best_score * 0.7 + 0.1
    else:
        confidence = best_score * 0.6
    
    return best_room, "PATTERN-MASTER", confidence

def choose_room_fusion() -> Tuple[int, str, float]:
    # Kết hợp multiple approaches
    quantum_room, quantum_algo, quantum_conf = choose_room_quantum()
    pattern_room, pattern_algo, pattern_conf = choose_room_pattern()
    fusion_scores = {}
    
    for room_id in ROOM_ORDER:
        quantum_analysis = calculate_room_potential(room_id)
        trend_analysis = analyze_trend_pattern(room_id)
        crowd_analysis = analyze_crowd_behavior(room_id)
        fusion_score = (
            quantum_analysis['total_score'] * 0.35 +
            trend_analysis * 0.30 +
            crowd_analysis * 0.25 +
            quantum_analysis['survival_rate'] * 0.10
        )
        
        fusion_scores[room_id] = fusion_score
    
    best_room, best_score = max(fusion_scores.items(), key=lambda x: x[1])
    if quantum_room == pattern_room == best_room:
        confidence = (quantum_conf + pattern_conf + best_score) / 3 + 0.15
        algo_name = "FUSION-CONSENSUS"
    elif quantum_room == best_room or pattern_room == best_room:
        confidence = (max(quantum_conf, pattern_conf) + best_score) / 2 + 0.08
        algo_name = "FUSION-HYBRID"
    else:
        confidence = best_score * 0.7
        algo_name = "FUSION-ADVANCED"
    
    return best_room, algo_name, min(0.95, confidence)

def choose_room_predator() -> Tuple[int, str, float]:
    prey_scores = {}
    
    for room_id in ROOM_ORDER:
        analysis = calculate_room_potential(room_id)
        survival_potential = analysis['survival_rate']
        trend_potential = analysis['trend']
        crowd_safety = analyze_crowd_behavior(room_id)
        risk_level = calculate_risk_factor(room_id)
        predator_score = (
            survival_potential * 0.3 +
            trend_potential * 0.25 +
            crowd_safety * 0.25 +
            (1 - risk_level) * 0.2
        )
        
        prey_scores[room_id] = predator_score
    
    if not prey_scores:
        return random.choice(ROOM_ORDER), "PREDATOR-FALLBACK", 0.5
    
    best_room, best_score = max(prey_scores.items(), key=lambda x: x[1])
    
    sorted_scores = sorted(prey_scores.values(), reverse=True)
    if len(sorted_scores) > 1:
        dominance = (sorted_scores[0] - sorted_scores[1]) * 4.0
        confidence = best_score * 0.6 + min(0.3, dominance)
    else:
        confidence = best_score * 0.6
    analysis = calculate_room_potential(best_room)
    if analysis['risk'] < 0.3:
        confidence += 0.1
    if analysis['crowd'] > 0.6:
        confidence += 0.05
    
    return best_room, "PREDATOR-INSTINCT", min(0.95, confidence)

def get_meta_boost() -> float:
    return random.uniform(0.01, 0.06)

def _room_features(rid: int):
    st = room_state.get(rid, {})
    analysis = calculate_room_potential(rid)
    
    return {
        "players": st.get("players", 0),
        "bet": st.get("bet", 0),
        "survival_rate": analysis['survival_rate'],
        "trend_score": analysis['trend'],
        "crowd_score": analysis['crowd'],
        "risk_score": analysis['risk'],
        "total_potential": analysis['total_score'],
        "confidence": analysis['confidence']
    }

def on_message(ws, message):
    global issue_id, count_down, killed_room, round_index, ui_state, analysis_start_ts, issue_start_ts
    global prediction_locked, predicted_room, last_killed_room, last_msg_ts, current_bet
    global win_streak, lose_streak, max_win_streak, max_lose_streak, cumulative_profit, _skip_rounds_remaining, stop_flag, analysis_blur
    
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
                bet = int(rm.get("total_bet_amount") or rm.get("totalBet") or rm.get("bet") or 0) or 0
                room_state[rid] = {"players": players, "bet": bet}
                room_stats[rid]["last_players"] = players
                room_stats[rid]["last_bet"] = bet
                
                ts = time.time()
                room_hist[rid].append({
                    "ts": ts,
                    "players": players,
                    "bet": bet
                })
                
            if new_issue is not None and new_issue != issue_id:
                log_debug(f"New issue: {issue_id} -> {new_issue}")
                issue_id = new_issue
                issue_start_ts = time.time()
                round_index += 1
                killed_room = None
                prediction_locked = False
                predicted_room = None
                ui_state = "ANALYZING"
                analysis_start_ts = time.time()

        elif msg_type == "notify_count_down" or "count_down" in msg_type:
            count_down = data.get("count_down") or data.get("countDown") or data.get("count") or count_down
            try:
                count_val = int(count_down)
            except Exception:
                count_val = None
                
            if count_val is not None:
                try:
                    if count_val <= 8 and not prediction_locked:
                        analysis_blur = False
                        lock_prediction_if_needed()
                    elif count_val <= 45:
                        ui_state = "ANALYZING"
                        analysis_start_ts = time.time()
                        analysis_blur = True
                except Exception:
                    pass

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
                global stop_flag
                try:
                    if stop_when_profit_reached and profit_target is not None and isinstance(current_build, (int, float)) and current_build >= profit_target:
                        console.print(f"[bold green]🎉 MỤC TIÊU LÃI ĐẠT: {current_build} >= {profit_target}. Dừng tool.[/]")
                        stop_flag = True
                        try:
                            wsobj = _ws.get("ws")
                            if wsobj:
                                wsobj.close()
                        except Exception:
                            pass
                    if stop_when_loss_reached and stop_loss_target is not None and isinstance(current_build, (int, float)) and current_build <= stop_loss_target:
                        console.print(f"[bold red]⚠️ STOP-LOSS TRIGGED: {current_build} <= {stop_loss_target}. Dừng tool.[/]")
                        stop_flag = True
                        try:
                            wsobj = _ws.get("ws")
                            if wsobj:
                                wsobj.close()
                        except Exception:
                            pass
                except Exception:
                    pass
            threading.Timer(1.2, _check_stop_conditions).start()

    except Exception as e:
        log_debug(f"on_message err: {e}")

def lock_prediction_if_needed(force: bool = False):
    global prediction_locked, predicted_room, ui_state, current_bet, _rounds_placed_since_skip, skip_next_round_flag, _skip_rounds_remaining, _skip_active_issue
    
    if stop_flag:
        return
    if prediction_locked and not force:
        return
    if issue_id is None:
        return
    
    if _skip_rounds_remaining > 0:
        if _skip_active_issue != issue_id:
            console.print(f"[yellow]⏸️ Đang nghỉ {_skip_rounds_remaining} ván theo cấu hình sau khi thua.[/]")
            _skip_rounds_remaining -= 1
            _skip_active_issue = issue_id

        prediction_locked = True
        ui_state = "ANALYZING"
        return
    
    algo_sel = settings.get("algo")

    if algo_sel == "FUSION":
        chosen, algo_used, conf = choose_room_fusion()
    elif algo_sel == "QUANTUM":
        chosen, algo_used, conf = choose_room_quantum()
    elif algo_sel == "PATTERN":
        chosen, algo_used, conf = choose_room_pattern()
    elif algo_sel == "PREDATOR":
        chosen, algo_used, conf = choose_room_predator()
    else:
        chosen, algo_used = choose_room_vip()
        conf = 0.12
    if algo_sel in ["FUSION", "PREDATOR"]:
        min_conf = 0.50
        if lose_streak == 2:
            min_conf = 0.60
        elif lose_streak >= 3:
            min_conf = 0.70
    elif algo_sel in ["QUANTUM", "PATTERN"]:
        min_conf = 0.45
        if lose_streak == 2:
            min_conf = 0.55
        elif lose_streak >= 3:
            min_conf = 0.65
    else:
        min_conf = 0.02
        if lose_streak == 2:
            min_conf = 0.05
        elif lose_streak >= 3:
            min_conf = 0.07
            
    if conf < min_conf:
        console.print(f"[yellow]⏸️ BỎ QUA ván này (Mức độ tin cậy={conf:.3f} < {min_conf:.2f}).[/]")
        prediction_locked = True
        ui_state = "ANALYZING"
        return
    if lose_streak >= 2:
        risk_factor = calculate_risk_factor(chosen)
        if risk_factor > 0.5:
            console.print(f"[yellow]⏸️ STREAK PROTECTION: Phòng {chosen} có rủi ro cao ({risk_factor:.3f}) khi đang thua {lose_streak} ván liên tiếp.[/]")
            prediction_locked = True
            ui_state = "ANALYZING"
            return
    
    predicted_room = chosen
    prediction_locked = True
    ui_state = "PREDICTED"
    
    if run_mode == "AUTO" and not skip_next_round_flag:
        bld, _, _ = fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
        if bld is None:
            console.print("[yellow]⚠️ Không lấy được số dư trước khi đặt — bỏ qua đặt ván này.[/]")
            prediction_locked = False
            return
        
        global current_bet
        if current_bet is None:
            current_bet = base_bet
        
        amt = float(current_bet)
        if algo_sel in ["FUSION", "PREDATOR"] and conf is not None:
            meta_boost_rate = get_meta_boost()
            boost = 1.0 + meta_boost_rate * float(conf)
            amt *= boost
            amt = min(amt, SELECTION_CONFIG.get("max_bet_allowed", float("inf")))
            amt = float(f"{amt:.4f}")
            console.print(f"[magenta]🧠 PRO BOOST: {conf:.3f} confidence → +{meta_boost_rate*100:.1f}% = {amt:.4f} BUILD[/magenta]")
        
        console.print(f"[cyan]💰 Đặt cược: {amt} BUILD (base={current_bet}, multiplier={multiplier})[/cyan]")
        if amt <= 0:
            console.print("[yellow]⚠️ Số tiền đặt không hợp lệ (<=0). Bỏ qua.[/]")
            prediction_locked = False
            return
            
        place_bet_async(issue_id, predicted_room, amt, algo_used=algo_used)
        _rounds_placed_since_skip += 1
        if bet_rounds_before_skip > 0 and _rounds_placed_since_skip >= bet_rounds_before_skip:
            skip_next_round_flag = True
            _rounds_placed_since_skip = 0
    elif skip_next_round_flag:
        console.print("[yellow]⏸️ TẠM DỪNG THEO DÕI SÁT THỦ[/]")
        skip_next_round_flag = False

def choose_room_vip() -> Tuple[int, str]:
    """Giữ lại thuật toán VIP gốc cho tương thích"""
    cand = [r for r in ROOM_ORDER]
    seed = 1234567
    rng = random.Random(seed)
    formulas = []
    for i in range(50):
        w_players = rng.uniform(0.2, 0.8)
        w_bet = rng.uniform(0.1, 0.6)
        w_bpp = rng.uniform(0.05, 0.6)
        w_survive = rng.uniform(0.05, 0.4)
        w_recent = rng.uniform(0.05, 0.3)
        w_last = rng.uniform(0.1, 0.6)
        noise_scale = rng.uniform(0.0, 0.08)
        formulas.append((w_players, w_bet, w_bpp, w_survive, w_recent, w_last, noise_scale))

    agg_scores = {r: 0.0 for r in cand}
    for idx, wset in enumerate(formulas):
        for r in cand:
            f = _room_features(r)
            score = 0.0
            score += wset[0] * (f.get("players", 0) / 50.0)
            score += wset[1] * (1.0 / (1.0 + f.get("bet", 0) / 2000.0))
            score += wset[2] * (1.0 / (1.0 + (f.get("bet", 0) / max(f.get("players", 1), 1)) / 1200.0))
            score += wset[3] * f.get("survival_rate", 0.5)
            score -= wset[4] * 0.1
            score -= wset[5] * (0.35 if last_killed_room == r else 0.0)
            noise = (math.sin((idx + 1) * (r + 1) * 12.9898) * 43758.5453) % 1.0
            noise = (noise - 0.5) * (wset[6] * 2.0)
            score += noise
            agg_scores[r] += score

    for r in agg_scores:
        agg_scores[r] /= len(formulas)

    ranked = sorted(agg_scores.items(), key=lambda kv: (-kv[1], kv[0]))
    best_room = ranked[0][0]
    return best_room, "VIP"

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

def _background_fetch_balance_after_result():
    try:
        fetch_balances_3games()
    except Exception:
        pass

def _mark_bet_result_from_issue(res_issue: Optional[int], krid: int):
    global current_bet, win_streak, lose_streak, max_win_streak, max_lose_streak, cumulative_profit, _skip_rounds_remaining, stop_flag, _skip_active_issue
    global total_wins, total_losses, win_rate 

    if res_issue is None:
        return

    if res_issue not in bet_sent_for_issue:
        log_debug(f"_mark_bet_result_from_issue: skip issue {res_issue} (no bet placed)")
        return

    rec = next((b for b in reversed(bet_history) if b.get("issue") == res_issue), None)
    if rec is None:
        log_debug(f"_mark_bet_result_from_issue: no record found for issue {res_issue}, skip")
        return

    if rec.get("settled"):
        log_debug(f"_mark_bet_result_from_issue: issue {res_issue} already settled, skip")
        return

    try:
        placed_room = int(rec.get("room"))
        if placed_room != int(krid):
            rec["result"] = "Thắng"
            rec["settled"] = True
            current_bet = base_bet
            win_streak += 1
            lose_streak = 0
            if win_streak > max_win_streak:
                max_win_streak = win_streak
            total_wins += 1
            total_games = total_wins + total_losses
            win_rate = (total_wins / total_games) * 100 if total_games > 0 else 0.0
            
        else:
            rec["result"] = "Thua"
            rec["settled"] = True
            try:
                old_bet = current_bet
                current_bet = float(rec.get("amount")) * float(multiplier)
                console.print(f"[red]🔴 THUA! Số cũ: {rec.get('amount')} × {multiplier} = {current_bet} BUILD[/red]")
            except Exception as e:
                current_bet = base_bet
                console.print(f"[red]🔴 THUA! Lỗi tính toán: {e}, reset về: {current_bet} BUILD[/red]")
            lose_streak += 1
            win_streak = 0
            if lose_streak > max_lose_streak:
                max_lose_streak = lose_streak
            total_losses += 1
            total_games = total_wins + total_losses
            win_rate = (total_wins / total_games) * 100 if total_games > 0 else 0.0
            
            if pause_after_losses > 0:
                _skip_rounds_remaining = pause_after_losses
                _skip_active_issue = None
    except Exception as e:
        log_debug(f"_mark_bet_result_from_issue err: {e}")
    finally:
        try:
            bet_sent_for_issue.discard(res_issue)
        except Exception:
            pass

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

def api_headers() -> Dict[str, str]:
    return {
        "content-type": "application/json",
        "user-agent": "Mozilla/5.0",
        "user-id": str(USER_ID) if USER_ID else "",
        "user-secret-key": SECRET_KEY if SECRET_KEY else ""
    }

def place_bet_http(issue: int, room_id: int, amount: float) -> dict:
    if betting_mode == "DEMO":
        import time
        import random
        time.sleep(random.uniform(0.1, 0.3))
        return {
            "msg": "ok",
            "code": 0,
            "status": "success",
            "demo": True,
            "data": {
                "issue": issue,
                "room_id": room_id,
                "amount": amount,
                "timestamp": time.time()
            }
        }
    else:
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
    rec = {"issue": issue, "room": room_id, "amount": float(amount), "time": now, "resp": resp, "result": "Đang", "algo": algo_used, "delta": 0.0, "win_streak": win_streak, "lose_streak": lose_streak}
    bet_history.append(rec)
    return rec

def place_bet_async(issue: int, room_id: int, amount: float, algo_used: Optional[str] = None):
    def worker():
        room_text = room_label(room_id)
        mode_icon = "🎮" if betting_mode == "💰" else "💰"
        console.print(f"[cyan]{mode_icon} {betting_mode} - Đang đặt {amount} BUILD -> {room_text} (v{issue}) — Thuật toán: {algo_used}[/]")
        time.sleep(random.uniform(0.02, 0.25))
        res = place_bet_http(issue, room_id, amount)
        rec = record_bet(issue, room_id, amount, res, algo_used=algo_used)
        if isinstance(res, dict) and (res.get("msg") == "ok" or res.get("code") == 0 or res.get("status") in ("ok", 1)):
            bet_sent_for_issue.add(issue)
            mode_icon = "🎮" if betting_mode == "💰" else "💰"
            console.print(f"[green]✅ {betting_mode} - Đặt thành công {amount} BUILD vào {room_text} (v{issue}).[/]")
        else:
            mode_icon = "🎮" if betting_mode == "💰" else "💰"
            console.print(f"[red]❌ {betting_mode} - Đặt lỗi v{issue}: {res}[/]")
    threading.Thread(target=worker, daemon=True).start()

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

def on_open(ws):
    _ws["ws"] = ws
    console.print("[green]ĐANG TRUY CẬP DỮ LIỆU GAME[/]")
    safe_send_enter_game(ws)

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
        time.sleep(t)
        backoff = min(backoff * 1.5, 30)

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
                if first_time or abs(delta) > 0:
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

def monitor_loop():
    global last_balance_fetch_ts, last_msg_ts, stop_flag
    while not stop_flag:
        now = time.time()
        if now - last_balance_fetch_ts >= BALANCE_POLL_INTERVAL:
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
        if now - last_msg_ts > 30:
            log_debug("No ws msg >30s, force reconnect")
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

def _spinner_char():
    return _spinner[int(time.time() * 4) % len(_spinner)]

def _rainbow_border_style() -> str:
    idx = int(time.time() * 2) % len(RAINBOW_COLORS)
    return RAINBOW_COLORS[idx]

def build_header(border_color: Optional[str] = None):
    tbl = Table.grid(expand=True)
    tbl.add_column(ratio=2)
    tbl.add_column(ratio=1)

    mode_icon = "🎮" if betting_mode == "💰" else "💰"
    left = Text(f"{mode_icon} {betting_mode} - VUA THOÁT HIỂM VIP BY HCODE", style="bold cyan")

    b = f"{current_build:,.4f}" if isinstance(current_build, (int, float)) else (str(current_build) if current_build is not None else "-")
    u = f"{current_usdt:,.4f}" if isinstance(current_usdt, (int, float)) else (str(current_usdt) if current_usdt is not None else "-")
    x = f"{current_world:,.4f}" if isinstance(current_world, (int, float)) else (str(current_world) if current_world is not None else "-")

    pnl_val = cumulative_profit if cumulative_profit is not None else 0.0
    pnl_str = f"{pnl_val:+,.4f}"
    pnl_style = "green bold" if pnl_val > 0 else ("red bold" if pnl_val < 0 else "yellow")

    bal = Text.assemble((f"USDT: {u}", "bold"), ("   "), (f"XWORLD: {x}", "bold"), ("   "), (f"BUILD: {b}", "bold"))

    algo_label = ADVANCED_ALGORITHMS.get(settings.get('algo'), settings.get('algo'))

    right_lines = []
    right_lines.append(f"Thuật toán: {algo_label}")
    right_lines.append(f"Lãi/lỗ: [{pnl_style}] {pnl_str} [/{pnl_style}]")
    right_lines.append(f"Phiên: {issue_id or '-'}")
    right_lines.append(f"Thống kê: {total_wins}✓/{total_losses}✗ ({win_rate:.1f}%)")
    right_lines.append(f"Chuỗi: W={max_win_streak} / L={max_lose_streak}")
    
    if stop_when_profit_reached and profit_target is not None:
        right_lines.append(f"[green]TakeProfit@{profit_target}[/]")
    if stop_when_loss_reached and stop_loss_target is not None:
        right_lines.append(f"[red]StopLoss@{stop_loss_target}[/]")

    right = Text.from_markup("\n".join(right_lines))

    tbl.add_row(left, right)
    tbl.add_row(bal, Text(f"{datetime.now(tz).strftime('%H:%M:%S')}  •  {_spinner_char()}", style="dim"))
    panel = Panel(tbl, box=box.ROUNDED, padding=(0,1), border_style=(border_color or _rainbow_border_style()))
    return panel

def build_rooms_table(border_color: Optional[str] = None):
    t = Table(box=box.MINIMAL, expand=True)
    t.add_column("ID", justify="center", width=3)
    t.add_column("Phòng", width=16)
    t.add_column("Ng", justify="right")
    t.add_column("Cược", justify="right")
    t.add_column("TT", justify="center")
    for r in ROOM_ORDER:
        st = room_state.get(r, {})
        status = ""
        try:
            if killed_room is not None and int(r) == int(killed_room):
                status = "[red]☠ Kill[/]"
        except Exception:
            pass
        try:
            if predicted_room is not None and int(r) == int(predicted_room):
                status = (status + " [dim]|[/] [green]✓ Dự đoán[/]") if status else "[green]✓ Dự đoán[/]"
        except Exception:
            pass
        players = str(st.get("players", 0))
        bet_val = st.get('bet', 0) or 0
        bet_fmt = f"{int(bet_val):,}"
        t.add_row(str(r), ROOM_NAMES.get(r, f"Phòng {r}"), players, bet_fmt, status)
    return Panel(t, title="PHÒNG", border_style=(border_color or _rainbow_border_style()))

def build_mid(border_color: Optional[str] = None):
    global analysis_start_ts, analysis_blur
    if ui_state == "ANALYZING":
        lines = []
        lines.append(f"ĐANG PHÂN TÍCH PHÒNG AN TOÀN NHẤT  {_spinner_char()}")
        if count_down is not None:
            try:
                cd = int(count_down)
                lines.append(f"Đếm ngược tới kết quả: {cd}s")
            except Exception:
                pass
        else:
            lines.append("Chưa nhận được dữ liệu đếm ngược...")

        if analysis_blur:
            bar_len = 36
            blocks = []
            tbase = int(time.time() * 5)
            for i in range(bar_len):
                val = (tbase + i) % 7
                ch = "█" if val in (0, 1, 2) else ("▓" if val in (3, 4) else "░")
                color = RAINBOW_COLORS[(i + tbase) % len(RAINBOW_COLORS)]
                blocks.append(f"[{color}]{ch}[/{color}]")
            lines.append("".join(blocks))
            lines.append("")
            lines.append("AI PRO ĐANG TÍNH TOÁN 8S CUỐI VÀO BUID")
        else:
            bar_len = 24
            filled = int((time.time() * 2) % (bar_len + 1))
            bars = []
            for i in range(bar_len):
                if i < filled:
                    color = RAINBOW_COLORS[i % len(RAINBOW_COLORS)]
                    bars.append(f"[{color}]█[/{color}]")
                else:
                    bars.append("·")
            lines.append("".join(bars))

        lines.append("")
        lines.append(f"Phòng sát thủ vào ván trước: {ROOM_NAMES.get(last_killed_room, '-')}")
        lines.append(f"Thống kê: {total_wins}✓/{total_losses}✗ ({win_rate:.1f}%)")
        
        txt = "\n".join(lines)
        return Panel(Align.center(Text.from_markup(txt), vertical="middle"), title="PHÂN TÍCH PRO", border_style=(border_color or _rainbow_border_style()))

    elif ui_state == "PREDICTED":
        name = ROOM_NAMES.get(predicted_room, f"Phòng {predicted_room}") if predicted_room else '-'
        last_bet_amt = current_bet if current_bet is not None else '-'
        lines = []
        lines.append(f"AI PRO chọn: {name}  — [green]KẾT QUẢ DỰ ĐOÁN[/]")
        lines.append(f"Số đặt: {last_bet_amt} BUILD")
        lines.append(f"Phòng sát thủ vào ván trước: {ROOM_NAMES.get(last_killed_room, '-')}")
        lines.append(f"Chuỗi thắng: {win_streak}  |  Chuỗi thua: {lose_streak}")
        lines.append(f"Thống kê: {total_wins}✓/{total_losses}✗ ({win_rate:.1f}%)")
        
        lines.append("")
        if count_down is not None:
            try:
                cd = int(count_down)
                lines.append(f"Đếm ngược tới kết quả: {cd}s")
            except Exception:
                pass
        lines.append("")
        lines.append(f"đang học hỏi dữ liệu {_spinner_char()}")
        txt = "\n".join(lines)
        return Panel(Align.center(Text.from_markup(txt)), title="DỰ ĐOÁN PRO", border_style=(border_color or _rainbow_border_style()))

    elif ui_state == "RESULT":
        k = ROOM_NAMES.get(killed_room, "-") if killed_room else "-"
        last_success = next((str(b.get('amount')) for b in reversed(bet_history) if b.get('result') in ('Thắng', 'Win')), '-')
        lines = []
        lines.append(f"Sát thủ đã vào: {k}")
        lines.append(f"Lãi/lỗ: {cumulative_profit:+.4f} BUILD")
        lines.append(f"Đặt cược thành công (last): {last_success}")
        lines.append(f"Thống kê: {total_wins}✓/{total_losses}✗ ({win_rate:.1f}%)")
        lines.append(f"Max Chuỗi: W={max_win_streak} / L={max_lose_streak}")
        
        txt = "\n".join(lines)
        border = None
        last = None
        if bet_history:
            last = bet_history[-1].get('result')
        if last == 'Thắng':
            border = 'green'
        elif last == 'Thua':
            border = 'red'
        return Panel(Align.center(Text.from_markup(txt)), title="KẾT QUẢ", border_style=(border or (border_color or _rainbow_border_style())))
    else:
        lines = []
        lines.append("Chờ ván mới...")
        lines.append(f"Phòng sát thủ vào ván trước: {ROOM_NAMES.get(last_killed_room, '-')}")
        lines.append(f"AI PRO chọn: {ROOM_NAMES.get(predicted_room, '-') if predicted_room else '-'}")
        lines.append(f"Lãi/lỗ: {cumulative_profit:+.4f} BUILD")
        lines.append(f"Thống kê: {total_wins}✓/{total_losses}✗ ({win_rate:.1f}%)")
        
        txt = "\n".join(lines)
        return Panel(Align.center(Text.from_markup(txt)), title="TRẠNG THÁI PRO", border_style=(border_color or _rainbow_border_style()))

def build_bet_table(border_color: Optional[str] = None):
    t = Table(title="Lịch sử cược (5 ván gần nhất)", box=box.SIMPLE, expand=True)
    t.add_column("Ván", no_wrap=True)
    t.add_column("Phòng", no_wrap=True)
    t.add_column("Tiền", justify="right", no_wrap=True)
    t.add_column("KQ", no_wrap=True)
    t.add_column("Thuật toán", no_wrap=True)
    last5 = list(bet_history)[-5:]
    for b in reversed(last5):
        amt = b.get('amount') or 0
        amt_fmt = f"{float(amt):,.4f}"
        res = str(b.get('result') or '-')
        algo = str(b.get('algo') or '-')
        if res.lower().startswith('thắng') or res.lower().startswith('win'):
            res_text = Text(res, style="green")
            row_style = ""
        elif res.lower().startswith('thua') or res.lower().startswith('lose'):
            res_text = Text(res, style="red")
            row_style = ""
        else:
            res_text = Text(res, style="yellow")
            row_style = ""
        t.add_row(str(b.get('issue') or '-'), str(b.get('room') or '-'), amt_fmt, res_text, algo)
    return Panel(t, border_style=(border_color or _rainbow_border_style()))

def prompt_settings():
    global base_bet, multiplier, run_mode, bet_rounds_before_skip, current_bet, pause_after_losses, profit_target, stop_when_profit_reached, stop_loss_target, stop_when_loss_reached, settings
    global total_wins, total_losses, win_rate 
    total_wins = 0
    total_losses = 0
    win_rate = 0.0
    
    console.print(Rule("[bold cyan]CẤU HÌNH NHANH - PRO VERSION[/]"))
    base = safe_input("Số BUILD đặt mỗi ván: ", default="1")
    try:
        base_bet = float(base)
    except Exception:
        base_bet = 1.0
        
    m = safe_input("Nhập 1 số nhân sau khi thua (ổn định thì 2): ", default="2")
    try:
        multiplier = float(m)
    except Exception:
        multiplier = 2.0
        
    current_bet = base_bet

    console.print("\n[bold]Chọn chế độ cược:[/]")
    console.print("1) DEMO - Giả lập đặt cược (không mất tiền thật)")
    console.print("2) REAL - Đặt cược thật (mất tiền thật)")
    mode = safe_input("Chọn (1/2): ", default="1")
    global betting_mode
    betting_mode = "REAL" if str(mode).strip() == "2" else "DEMO"
    console.print(f"[bold green]Chế độ: {betting_mode}[/bold green]")

    console.print("\n[bold]Chọn thuật toán PRO:[/]")
    console.print("1) FUSION - Hệ thống AI tổng hợp thông minh")
    console.print("2) QUANTUM - Quantum AI siêu việt")
    console.print("3) PATTERN - Master phân tích pattern") 
    console.print("4) PREDATOR - Predator Instinct AI")
    console.print("5) Bản thường - Thuật toán cơ bản")
    
    alg = safe_input("Chọn (1/2/3/4/5): ", default="1")
    algo_map = {
        "1": "FUSION", "2": "QUANTUM", "3": "PATTERN", 
        "4": "PREDATOR", "5": "BASIC"
    }
    settings["algo"] = algo_map.get(str(alg).strip(), "FUSION")
    console.print(f"[bold green]Đã chọn: {ADVANCED_ALGORITHMS.get(settings['algo'], settings['algo'])}[/bold green]")

    s = safe_input("Chống soi: sau bao nhiêu ván đặt thì nghỉ 1 ván: ", default="0")
    try:
        bet_rounds_before_skip = int(s)
    except Exception:
        bet_rounds_before_skip = 0
        
    pl = safe_input("Nếu thua thì nghỉ bao nhiêu tay trước khi cược lại (ví dụ 2): ", default="0")
    try:
        pause_after_losses = int(pl)
    except Exception:
        pause_after_losses = 0
        
    pt = safe_input("lãi bao nhiêu thì chốt( không dùng enter): ", default="")
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
        
    sl = safe_input("lỗ bao nhiêu thì chốt( không dùng enter): ", default="")
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

    runm = safe_input("💯bạn đã sẵn sàng hãy nhấn enter để bắt đầu💯: ", default="AUTO")
    run_mode = str(runm).upper()

def start_threads():
    threading.Thread(target=start_ws, daemon=True).start()
    threading.Thread(target=monitor_loop, daemon=True).start()

def parse_login():
    global USER_ID, SECRET_KEY
    console.print(Rule("[bold cyan]ĐĂNG NHẬP[/]"))
    link = safe_input("Dán link trò chơi (từ xworld.info) tại đây (ví dụ chứa userId & secretKey) > ", default=None)
    if not link:
        console.print("[red]Không nhập link. Thoát.[/]")
        sys.exit(1)
    try:
        parsed = urlparse(link)
        params = parse_qs(parsed.query)
        if 'userId' in params:
            USER_ID = int(params.get('userId')[0])
        SECRET_KEY = params.get('secretKey', [None])[0]
        console.print(f"[green]✅ Đã đọc: userId={USER_ID}[/]")
    except Exception as e:
        console.print("[red]Link không hợp lệ. Thoát.[/]")
        log_debug(f"parse_login err: {e}")
        sys.exit(1)

def main():
    parse_login()
    console.print("[bold magenta]Loading PRO VERSION...[/]")
    prompt_settings()
    console.print("[bold green]Bắt đầu kết nối dữ liệu với thuật toán PRO...[/]")

    def on_balance_changed(bal, delta, info):
        console.print(f"[green]⤴️ cập nhật số dư: {bal:.4f} (Δ {delta:+.4f}) — {info.get('ts')}[/]")

    def on_error(msg):
        console.print(f"[red]Balance poll lỗi: {msg}[/]")

    poller = BalancePoller(USER_ID, SECRET_KEY, poll_seconds=max(1, int(BALANCE_POLL_INTERVAL)), on_balance=on_balance_changed, on_error=on_error, on_status=None)
    poller.start()
    start_threads()

    with Live(Group(build_header(), build_mid(), build_rooms_table(), build_bet_table()), refresh_per_second=8, console=console, screen=False) as live:
        try:
            while not stop_flag:
                live.update(Group(build_header(), build_mid(), build_rooms_table(), build_bet_table()))
                time.sleep(0.12)
            console.print("[bold yellow]Tool đã dừng theo yêu cầu hoặc đạt mục tiêu.[/]")
        except KeyboardInterrupt:
            console.print("[yellow]Thoát bằng người dùng.[/]")
            poller.stop()