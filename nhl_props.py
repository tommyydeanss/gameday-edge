"""NHL player points projections for the Game Day Board.

Imported by nfl_board.py. Data: the NHL's public APIs (api-web.nhle.com schedule and rosters,
api.nhle.com/stats per-game skater logs and even-strength / power-play ice time), DailyFaceoff line
combinations (public team pages), and The Odds API (icehockey_nhl, player_points) for Hard Rock prices.

Model (backtested walk-forward on 2025-26, with 2024-25 as history):
  even-strength points/60 (shrunk toward what players with that ice time produce) x projected EV minutes
  + power-play points/60 (shrunk toward the league PP rate) x projected PP minutes
  x opponent goals-against factor x home ice.  P(over line) from a Poisson curve.
  Projected minutes = recent ice time, nudged toward what tonight's DailyFaceoff line and PP unit usually get.
  Knowing the actual night's line/PP role cut log-loss from 0.5911 to 0.5879 on Jan-Apr 2026 games
  (an upper bound); DailyFaceoff lines are applied at about half that strength (W_EV / W_PP).
"""
import json
import math
import time
import unicodedata
from collections import defaultdict
from datetime import date, datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

import requests

ET = ZoneInfo("America/New_York")
WEB = "https://api-web.nhle.com/v1"
STATS = "https://api.nhle.com/stats/rest/en/skater/summary"
TOI_REPORT = "https://api.nhle.com/stats/rest/en/skater/timeonice"
REALTIME_REPORT = "https://api.nhle.com/stats/rest/en/skater/realtime"
DFO = "https://www.dailyfaceoff.com"
ODDS_BASE = "https://api.the-odds-api.com/v4/sports/icehockey_nhl"
MARKETS = {"player_points": "pts", "player_shots_on_goal": "sog"}
CACHE = Path(__file__).resolve().parent / ".nfl_cache"
TEAMS = ["ANA", "BOS", "BUF", "CAR", "CBJ", "CGY", "CHI", "COL", "DAL", "DET", "EDM", "FLA", "LAK", "MIN", "MTL", "NJD",
         "NSH", "NYI", "NYR", "OTT", "PHI", "PIT", "SEA", "SJS", "STL", "TBL", "TOR", "UTA", "VAN", "VGK", "WPG", "WSH"]
PAST_DAYS = 14    # keep pre-game projections (and results) for this many past days
AHEAD_DAYS = 7    # project this many days ahead
BROWSER_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36"

# ---------------------------------------------------------------- model
P = dict(
    DECAY=0.995,       # per-game decay of a player's history
    PREV_W=0.6,        # weight carried over from the previous season
    K_EV=10.0,         # hours of EV ice time of role-based prior mixed into a player's EV points/60
    K_PP=3.0,          # hours of PP ice time of league PP rate mixed into a player's PP points/60
    TOI_DECAY=0.80,    # per-game decay for projected ice time (recent role matters most)
    TEAM_DECAY=0.99,
    TEAM_K=30.0,       # games of league average mixed into opponent goals against
    DEF_B=0.9,         # opponent goals-against strength
    HOME=1.02,
    W_EV=0.25,         # pull of EV minutes toward tonight's line slot (hindsight-best was 0.5)
    W_PP=0.40,         # pull of PP minutes toward tonight's PP unit (hindsight-best was 0.75)
    # shots on goal (tuned walk-forward on Oct-Jan 2025-26, scored on Jan-Apr: log-loss 0.438 vs 0.509 league-rate baseline)
    S_K=6.0,           # hours of role-based prior shot rate mixed into a player's shots/60
    S_PPW=3.0,         # a PP minute counts as this many EV minutes of shooting opportunity
    S_OPP_B=1.2,       # opponent shots-against strength
    S_OFF_B=0.3,       # own team shots-for strength
    S_HOME=1.02,
    S_B2B=0.95,        # second night of a back-to-back
    # rookies / little NHL history (tuned walk-forward Sep 29)
    K_T=6.0,           # NHL games at which half the pull toward tonight's line-slot minutes comes from his own history
    RK_S=0.20,         # rookie outside a top-6 / top-pair / PP1 role: this much lower starting shot rate (fades with games)
    RK_P=0.20,         # same for even-strength points
    # linemates, rink scorers, power-play chances (tuned walk-forward Sep 29; see board-status notes)
    LM_B=0.15,         # EV points x (tonight's linemates' EV points/60 / his usual linemates')^LM_B
    LM_S=0.20,         # shots x the same ratio^LM_S (better linemates -> more shots)
    LM_D=0.97,         # per-game decay of his "usual linemates" average
    RINK_B=0.5,        # shots x (this rink's recorded shots / expected)^RINK_B; his history is de-biased the same way
    RINK_K=60.0,       # games of neutral rink mixed into each rink's factor
    PP_B=0.15,         # PP minutes x (opponent's penalty-kill minutes per game / league)^PP_B
    PP_K=40.0,         # games of league average mixed into each team's PK minutes
    # Hard Rock game lines (added Oct 1): expected team goals implied by the moneyline + total
    S_KA=4.5,          # hours of role prior mixed into a player's shot ATTEMPTS per weighted hour (added Oct 1)
    K_C=400.0,         # attempts of his position's shots-on-goal share mixed into his own share
    MKT_W=0.5,         # points x (market team goals / model team goals)^MKT_W; can't be backtested (no past lines), so half weight
    MKT_CAP=0.15,      # never move a projection more than +-15% for this
)


def grp_of(pos):
    return "D" if pos == "D" else "F"


class State:
    """Decayed running sums per player and per team, updated game by game (walk-forward safe)."""

    def __init__(self, p=P):
        self.p = p
        self.pl, self.tm, self.rk = {}, {}, {}
        self.lg = 3.0
        self.fit = None

    def new_season(self):
        w = self.p["PREV_W"]
        for s in self.pl.values():
            for k in ("evs", "pps", "evp", "ppp", "tw", "tev", "tpp", "sh", "shw", "at", "shr"):
                if k in s:
                    s[k] *= w
            s["season_n"], s["recent"] = 0, []
        for t in self.tm.values():
            for k in ("w", "gf", "ga", "sf", "sa", "pp", "sh"):
                t[k] *= w
            t["dates"] = []
        for v in self.rk.values():
            v[0] *= w; v[1] *= w

    def fit_priors(self):
        """EV points/60 as a straight line in EV minutes (bigger role, higher prior); flat PP points/60. Per F and D."""
        fit = {}
        for g in ("F", "D"):
            xs, ys, ws, zs, pn, pd = [], [], [], [], 0.0, 0.0
            grp_sh = sum(s.get("shr", 0.0) for s in self.pl.values() if grp_of(s["pos"]) == g)
            grp_at = sum(s.get("at", 0.0) for s in self.pl.values() if grp_of(s["pos"]) == g)
            for s in self.pl.values():
                if grp_of(s["pos"]) != g or s["evs"] < 3600 * 5:
                    continue
                h = s["evs"] / 3600
                xs.append(s["tev"] / s["tw"]); ys.append(s["evp"] / h); ws.append(h)
                zs.append(s["sh"] / max(1e-9, s["shw"] / 3600))
                pn += s["ppp"]; pd += s["pps"] / 3600
            if len(xs) < 30:
                continue
            W = sum(ws); mx = sum(w * x for w, x in zip(ws, xs)) / W
            vx = sum(w * (x - mx) ** 2 for w, x in zip(ws, xs))

            def line(vals):
                my = sum(w * y for w, y in zip(ws, vals)) / W
                cxy = sum(w * (x - mx) * (y - my) for w, x, y in zip(ws, xs, vals))
                b = cxy / vx if vx else 0.0
                return my - b * mx, b
            a, b = line(ys)
            fit[g] = (a, b, pn / pd if pd else 4.0, line(zs), grp_sh / grp_at if grp_at else 0.52)
        self.fit = fit

    def rink(self, venue):
        """Shots recorded at this rink vs expected (1.0 = neutral), shrunk and softened by RINK_B."""
        v, p = self.rk.get(venue), self.p
        if not v:
            return 1.0
        K = p["RINK_K"] * 60
        return ((v[0] + K) / (v[1] + K)) ** p["RINK_B"]

    def pp_factor(self, opp):
        """How many more (or fewer) PP minutes than usual: the opponent's penalty-kill minutes per game vs league."""
        p, t = self.p, self.tm.get(opp)
        W = sum(x["w"] for x in self.tm.values()) or 1
        lpp = sum(x.get("sh", 0.0) for x in self.tm.values()) / W or 300.0
        if not t:
            return 1.0
        return ((t.get("sh", 0.0) + p["PP_K"] * lpp) / (t["w"] + p["PP_K"]) / lpp) ** p["PP_B"]

    def ev_rate(self, pid, pos):
        """His current EV points/60 estimate (used to rate him as someone's linemate)."""
        p, s, g = self.p, self.pl.get(pid), grp_of(pos)
        ev_m = s["tev"] / s["tw"] if s and s["tw"] else (15.0 if g == "D" else 10.0)
        a, b = (self.fit or {}).get(g, (2.0 if g == "F" else 0.9, 0.0))[:2]
        return ((s["evp"] if s else 0) + p["K_EV"] * max(0.2, a + b * ev_m)) / ((s["evs"] / 3600 if s else 0) + p["K_EV"])

    def project(self, pid, pos, opp, home, typ=None, team=None, b2b=False, top=False, lmq=None):
        """Expected points and shots tonight. typ = (typical EV min, typical PP min) for tonight's line/PP slot, if known."""
        p, s, g = self.p, self.pl.get(pid), grp_of(pos)
        if s and s["tw"] > 0:
            ev_m, pp_m = s["tev"] / s["tw"], s["tpp"] / s["tw"]
        else:
            ev_m, pp_m = (15.0, 0.5) if g == "D" else (10.0, 0.5)
        base_toi = ev_m + pp_m
        n = s["n"] if s else 0
        fresh = p["K_T"] / (p["K_T"] + n)     # 1 for a debut, 0.5 after K_T games, fades toward 0
        if typ:
            # little NHL history -> trust tonight's line / PP slot for his minutes much more than his few games
            w_ev = p["W_EV"] + (1 - p["W_EV"]) * fresh
            w_pp = p["W_PP"] + (1 - p["W_PP"]) * fresh
            ev_m = (1 - w_ev) * ev_m + w_ev * typ[0]
            pp_m = (1 - w_pp) * pp_m + w_pp * typ[1]
        ppf = self.pp_factor(opp)
        pp_m *= ppf
        lmf = 1.0
        if lmq and s and s.get("lmw", 0) > 0 and s["lmq"] > 0:
            lmf = lmq / (s["lmq"] / s["lmw"])
        rook_s = 1 - (0 if top else p["RK_S"]) * fresh
        rook_p = 1 - (0 if top else p["RK_P"]) * fresh
        a, b, ppr, sfit, conv_g = (self.fit or {}).get(g, (2.0 if g == "F" else 0.9, 0.0, 4.0, (8.0 if g == "F" else 5.0, 0.0), 0.52))
        r_ev = ((s["evp"] if s else 0) + p["K_EV"] * max(0.2, a + b * ev_m) * rook_p) / ((s["evs"] / 3600 if s else 0) + p["K_EV"])
        r_pp = ((s["ppp"] if s else 0) + p["K_PP"] * ppr) / ((s["pps"] / 3600 if s else 0) + p["K_PP"])
        t = self.tm.get(opp)
        dfn = (t["ga"] + p["TEAM_K"] * self.lg) / (t["w"] + p["TEAM_K"]) / self.lg if t else 1.0
        env = dfn ** p["DEF_B"] * (p["HOME"] if home else 1 / p["HOME"])
        pts = (r_ev * lmf ** p["LM_B"] * ev_m + r_pp * pp_m) / 60 * env
        toi = ev_m + pp_m
        # shots on goal: shots per "weighted" minute (PP minutes count S_PPW x), shrunk toward a role prior
        wmin = ev_m + p["S_PPW"] * pp_m
        prior_s = max(0.5, sfit[0] + sfit[1] * ev_m) * rook_s
        # shot rate built from shot ATTEMPTS (shots on goal + missed + blocked: steadier than shots alone) x his
        # share of attempts that reach the net; both shrunk toward his role / position (backtest Oct 1: 0.4371 -> 0.4365)
        at_ = s.get("at", 0.0) if s else 0.0
        r_a = (at_ + p["S_KA"] * prior_s / conv_g) / ((s["shw"] / 3600 if s else 0) + p["S_KA"])
        conv = ((s.get("shr", 0.0) if s else 0) + p["K_C"] * conv_g) / (at_ + p["K_C"])
        r_s = r_a * conv
        W = sum(x["w"] for x in self.tm.values()) or 1
        spg = sum(x["sf"] for x in self.tm.values()) / W or 29.0
        def rate(t_, k):
            return (t_[k] + p["TEAM_K"] * spg) / (t_["w"] + p["TEAM_K"]) / spg if t_ else 1.0
        own = self.tm.get(team) if team else None
        senv = rate(t, "sa") ** p["S_OPP_B"] * rate(own, "sf") ** p["S_OFF_B"] * (p["S_HOME"] if home else 1 / p["S_HOME"])
        if b2b:
            senv *= p["S_B2B"]
        rkf = self.rink(team if home else opp) if team else 1.0
        sog = r_s * wmin / 60 * senv * rkf * lmf ** p["LM_S"]
        return {"lmf": lmf, "rink": rkf, "ppf": ppf, "pts": pts, "toi": toi, "toi0": base_toi, "ev": ev_m, "pp": pp_m, "r_ev": r_ev, "r_pp": r_pp,
                "p60": (r_ev * ev_m + r_pp * pp_m) / toi if toi else 0.0, "env": env,
                "sog": sog, "s60": sog / toi * 60 if toi else 0.0, "senv": senv, "b2b": b2b}

    def update_rink(self, venue, shots_by_team):
        """After a game: shots recorded here (both teams) vs what these two teams usually get."""
        if len(shots_by_team) != 2:
            return
        W = sum(x["w"] for x in self.tm.values()) or 1
        lgs = sum(x["sf"] for x in self.tm.values()) / W or 29.0
        exp = sum((self.tm[t]["sf"] + 10 * lgs) / (self.tm[t]["w"] + 10) if t in self.tm else lgs for t in shots_by_team)
        v = self.rk.setdefault(venue, [0.0, 0.0])
        v[0] += sum(shots_by_team.values()); v[1] += exp

    def b2b(self, team, day):
        """Did the team also play the day before `day`?"""
        ds = (self.tm.get(team) or {}).get("dates") or []
        return bool(ds) and ds[-1] == (date.fromisoformat(day) - timedelta(days=1)).isoformat()

    def update_player(self, r, split, lmq=None, rkf=1.0, att=None):
        """r = skater-game row; split = (ev_sec, pp_sec, sh_sec) or None."""
        pid, name, team, pos = r[2], r[3], r[4], r[7]
        g, a, pts, sog, pp_pts, toi = r[8], r[9], r[10], r[11], r[12], r[13]
        ev, pp, sh = split if split else (toi, 0, 0)
        p = self.p
        s = self.pl.get(pid)
        if not s:
            s = self.pl[pid] = dict(evs=0.0, pps=0.0, evp=0.0, ppp=0.0, tw=0.0, tev=0.0, tpp=0.0, sh=0.0, shw=0.0, n=0, season_n=0, recent=[])
        for k in ("evs", "pps", "evp", "ppp", "sh", "shw"):
            s[k] *= p["DECAY"]
        s["at"] = s.get("at", 0.0) * p["DECAY"] + (att if att is not None else sog)
        s["shr"] = s.get("shr", 0.0) * p["DECAY"] + sog
        s["sh"] += sog / rkf; s["shw"] += (ev + sh) + p["S_PPW"] * pp
        s["evs"] += ev + sh; s["pps"] += pp
        s["ppp"] += pp_pts; s["evp"] += pts - pp_pts
        td = p["TOI_DECAY"]
        s["tw"] = s["tw"] * td + 1; s["tev"] = s["tev"] * td + (ev + sh) / 60; s["tpp"] = s["tpp"] * td + pp / 60
        s["n"] += 1; s["season_n"] += 1
        if lmq:
            s["lmq"] = s.get("lmq", 0.0) * p["LM_D"] + lmq; s["lmw"] = s.get("lmw", 0.0) * p["LM_D"] + 1
        s["recent"] = (s["recent"] + [(r[1], pts, a, round(toi / 60, 1), str(r[0]), sog)])[-10:]
        s.update(pos=pos, team=team, name=name, last=r[1])

    def update_team(self, team, gf, ga, day, sf=0, sa=0, pp=0, sh=0):
        t = self.tm.setdefault(team, dict(w=0.0, gf=0.0, ga=0.0, sf=0.0, sa=0.0, pp=0.0, sh=0.0, dates=[]))
        d = self.p["TEAM_DECAY"]
        t["pp"] = t.get("pp", 0.0) * d + pp; t["sh"] = t.get("sh", 0.0) * d + sh
        t["w"] = t["w"] * d + 1; t["gf"] = t["gf"] * d + gf; t["ga"] = t["ga"] * d + ga
        t["sf"] = t["sf"] * d + sf; t["sa"] = t["sa"] * d + sa
        t["dates"] = (t["dates"] + [day])[-10:]


def pois_over(lam, line):
    k, cdf, term = int(math.floor(line)), 0.0, math.exp(-lam)
    for i in range(k + 1):
        if i:
            term *= lam / i
        cdf += term
    return max(0.0, min(1.0, 1 - cdf))


def slot_minutes(rows, splits):
    """Typical EV and PP minutes by (F/D, line, PP unit), with each night's line/unit read from actual ice-time ranks."""
    by_tg = defaultdict(list)
    for r in rows:
        by_tg[(r[0], r[4])].append(r)
    acc = defaultdict(lambda: [0, 0.0, 0.0])
    for (gid, team), rs in by_tg.items():
        sp = {r[2]: splits.get((r[0], r[2])) for r in rs}
        if any(v is None for v in sp.values()):
            continue
        F = sorted((r for r in rs if r[7] != "D"), key=lambda r: -sp[r[2]][0])
        Dd = sorted((r for r in rs if r[7] == "D"), key=lambda r: -sp[r[2]][0])
        PPr = sorted(rs, key=lambda r: -sp[r[2]][1])
        line = {r[2]: min(4, i // 3 + 1) for i, r in enumerate(F)}
        line.update({r[2]: min(3, i // 2 + 1) for i, r in enumerate(Dd)})
        unit = {r[2]: (1 if i < 5 else 2 if i < 10 else 0) if sp[r[2]][1] > 0 else 0 for i, r in enumerate(PPr)}
        for r in rs:
            ev, pp, sh = sp[r[2]]
            a = acc[(grp_of(r[7]), line[r[2]], unit[r[2]])]
            a[0] += 1; a[1] += (ev + sh) / 60; a[2] += pp / 60
    return {k: (round(v[1] / v[0], 2), round(v[2] / v[0], 2)) for k, v in acc.items() if v[0] >= 50}


# ---------------------------------------------------------------- data
def _get(url, params=None, tries=3):
    for i in range(tries):
        try:
            r = requests.get(url, params=params, timeout=40, headers={"User-Agent": "game-day-board"})
            if r.status_code == 200:
                return r.json()
            if r.status_code == 404:
                return None
        except requests.RequestException:
            if i == tries - 1:
                raise
        time.sleep(1.5 * (i + 1))
    raise RuntimeError(f"NHL API request failed: {url}")


def season_id(today):
    y = today.year if today.month >= 8 else today.year - 1
    return f"{y}{y + 1}"


def _chunk(url, conv, season, a, b):
    """Every regular-season skater-game row of a stats report between dates a (incl) and b (excl)."""
    exp = f'seasonId={season} and gameTypeId=2 and gameDate>="{a}" and gameDate<"{b}"'
    j = _get(url, {"isAggregate": "false", "isGame": "true", "start": 0, "limit": -1, "cayenneExp": exp}) or {}
    data = j.get("data", [])
    if j.get("total", 0) >= 10000 or j.get("total", 0) != len(data):
        da, db = date.fromisoformat(a), date.fromisoformat(b)
        if (db - da).days > 1:
            mid = (da + (db - da) / 2).isoformat()
            return _chunk(url, conv, season, a, mid) + _chunk(url, conv, season, mid, b)
    return [conv(r) for r in data]


def _summary_row(r):
    return [r["gameId"], r["gameDate"], r["playerId"], r["skaterFullName"], r["teamAbbrev"], r["opponentTeamAbbrev"],
            r["homeRoad"], r["positionCode"], r["goals"] or 0, r["assists"] or 0, r["points"] or 0, r["shots"] or 0,
            r.get("ppPoints") or 0, r["timeOnIcePerGame"] or 0]


def _toi_row(r):
    return [r["gameId"], r["playerId"], r.get("evTimeOnIce") or 0, r.get("ppTimeOnIce") or 0, r.get("shTimeOnIce") or 0]


def _season_report(kind, url, conv, season, today):
    """A whole season of a per-game report. Two-week chunks that ended 3+ days ago are cached on disk."""
    CACHE.mkdir(exist_ok=True)
    path = CACHE / f"nhl_{kind}_{season}.json"
    try:
        cache = json.loads(path.read_text()) if path.exists() else {}
    except ValueError:
        cache = {}
    y = int(season[:4])
    d, end = date(y, 9, 25), min(date(y + 1, 6, 30), today + timedelta(days=1))
    rows = []
    while d < end:
        n = min(d + timedelta(days=14), end)
        key = f"{d}|{n}"
        if key in cache:
            part = cache[key]
        else:
            part = _chunk(url, conv, season, d.isoformat(), n.isoformat())
            if n <= today - timedelta(days=3):
                cache[key] = part
        rows += part
        d = n
    path.write_text(json.dumps(cache))
    return rows


def skater_games(season, today):
    rows = _season_report("skaters", STATS, _summary_row, season, today)
    rows.sort(key=lambda r: (r[1], r[0]))
    return rows


def _realtime_row(r):
    return [r["gameId"], r["playerId"], r.get("totalShotAttempts") or 0]


def shot_attempts(season, today):
    """{(gameId, playerId): total shot attempts} (shots on goal + missed + blocked)."""
    try:
        return {(r[0], r[1]): r[2] for r in _season_report("attempts", REALTIME_REPORT, _realtime_row, season, today)}
    except Exception as e:   # nice-to-have: the model falls back to shots on goal
        print(f"NHL: shot attempts unavailable ({e}); using shots on goal only.")
        return {}


def toi_splits(season, today):
    return {(r[0], r[1]): (r[2], r[3], r[4]) for r in _season_report("toi", TOI_REPORT, _toi_row, season, today)}


def schedule(first, last):
    """Games from first..last (dates, ET) from the weekly schedule endpoint."""
    games, d, seen = [], first, set()
    while d <= last:
        j = _get(f"{WEB}/schedule/{d.isoformat()}") or {}
        for wk in j.get("gameWeek", []):
            for g in wk.get("games", []):
                if g["id"] in seen or g.get("gameType") not in (2, 3):
                    continue
                seen.add(g["id"])
                start = datetime.fromisoformat(g["startTimeUTC"].replace("Z", "+00:00")).astimezone(ET)
                if not (first <= start.date() <= last):
                    continue
                a, h = g["awayTeam"], g["homeTeam"]
                games.append({"id": str(g["id"]), "day": start.date().isoformat(), "time": start.strftime("%H:%M"),
                              "away": a["abbrev"], "home": h["abbrev"], "state": g.get("gameState", "FUT"),
                              "as": a.get("score"), "hs": h.get("score"),
                              "_names": {a["abbrev"]: _team_name(a), h["abbrev"]: _team_name(h)}})
        d += timedelta(days=7)
    games.sort(key=lambda g: (g["day"], g["time"]))
    return games


def _team_name(t):
    place, common = (t.get("placeName") or {}).get("default", ""), (t.get("commonName") or {}).get("default", "")
    return f"{place} {common}".strip() or t.get("abbrev", "")


def rosters(season, goalies_out=None):
    """Skaters {id: info}; goalies (name, headshot) go into goalies_out[(team, norm name)] when given."""
    out = {}
    for t in TEAMS:
        j = _get(f"{WEB}/roster/{t}/{season}") or _get(f"{WEB}/roster/{t}/current") or {}
        if goalies_out is not None:
            for p_ in j.get("goalies", []):
                nm = f'{p_["firstName"]["default"]} {p_["lastName"]["default"]}'
                goalies_out[(t, norm_name(nm))] = {"id": p_["id"], "hs": p_.get("headshot", "")}
        for grp in ("forwards", "defensemen"):
            for p in j.get(grp, []):
                out[p["id"]] = {"team": t, "pos": p.get("positionCode", "C"), "hs": p.get("headshot", ""),
                                "name": f'{p["firstName"]["default"]} {p["lastName"]["default"]}'}
    return out


def norm_name(name):
    n = unicodedata.normalize("NFKD", name or "").encode("ascii", "ignore").decode().lower()
    n = "".join(c if c.isalnum() or c == " " else " " for c in n)
    return " ".join(w for w in n.split() if w not in ("jr", "sr", "ii", "iii", "iv"))


# ---------------------------------------------------------------- DailyFaceoff line combinations
def _next_data(html):
    i = html.find('id="__NEXT_DATA__"')
    if i < 0:
        return None
    i = html.find(">", i) + 1
    j = html.find("</script>", i)
    return json.loads(html[i:j])


def _dfo_page(path):
    r = requests.get(DFO + path, timeout=30, headers={"User-Agent": BROWSER_UA, "Accept": "text/html"})
    r.raise_for_status()
    return _next_data(r.text)


def dfo_team_slugs():
    nd = _dfo_page("/teams") or {}
    teams = nd.get("props", {}).get("pageProps", {}).get("leagueCapSummary", {}).get("teams", [])
    return {t["teamAbbreviation"]: t["team"] for t in teams if t.get("teamAbbreviation") and t.get("team")}


def compact_dfo(c):
    return {"source": c.get("sourceName"), "updatedAt": c.get("updatedAt"),
            "players": [{"name": p.get("name"), "pos": p.get("positionIdentifier"), "group": p.get("groupIdentifier"),
                         "cat": p.get("categoryIdentifier"), "inj": p.get("injuryStatus"), "gtd": bool(p.get("gameTimeDecision"))}
                        for p in c.get("players", [])]}


def fetch_dfo(teams):
    """Line combinations for the given team abbreviations: {abbr: compact}. Missing teams are skipped."""
    out, errors = {}, 0
    try:
        slugs = dfo_team_slugs()
    except (requests.RequestException, ValueError):
        return {}, "DailyFaceoff unreachable; lines not applied."
    for t in teams:
        slug = slugs.get(t)
        if not slug:
            continue
        try:
            nd = _dfo_page(f"/teams/{slug}/line-combinations")
            c = (nd or {}).get("props", {}).get("pageProps", {}).get("combinations")
            if c:
                out[t] = compact_dfo(c)
        except (requests.RequestException, ValueError):
            errors += 1
        time.sleep(0.4)   # be polite: one page at a time
    msg = f"DailyFaceoff lines for {len(out)} teams" + (f" ({errors} failed)" if errors else "")
    return out, msg + "."


def log_dfo(day, dfo):
    """Keep every day's lines so their real value can be backtested later."""
    if not dfo:
        return
    folder = CACHE / "dfo_lines"
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / f"{day}.json"
    try:
        old = json.loads(path.read_text()) if path.exists() else {}
    except ValueError:
        old = {}
    stamp = datetime.now(ET).strftime("%H:%M")
    for t, c in dfo.items():
        old.setdefault(t, {})[stamp] = c
    path.write_text(json.dumps(old))


def find_in_lineup(team_lu, *names):
    """Exact normalized name first; else same last name and same first initial (Zack/Zachary, Gabe/Gabriel)."""
    for n in names:
        e = team_lu.get(norm_name(n))
        if e:
            return e
    for n in names:
        parts = norm_name(n).split()
        if len(parts) < 2:
            continue
        cands = [e for k, e in team_lu.items() if k.split() and k.split()[-1] == parts[-1] and k[0] == parts[0][0]]
        if len(cands) == 1:
            return cands[0]
    return None


def lines_kind(source):
    s = (source or "").lower()
    if "confirm" in s:
        return "confirmed"
    if s in ("projected", "dfo projections") or s.startswith("training camp") or not s:
        return "projected"
    return "reported"


def lineup_map(team_dfo):
    """{norm name: info} for one team: line (1-4 F, 1-3 D), pp unit (0/1/2), status (out/dtd/None), gtd, goalie."""
    info = {}
    for p in team_dfo.get("players", []):
        k = norm_name(p["name"])
        e = info.setdefault(k, {"line": None, "pp": 0, "status": None, "gtd": False, "name": p["name"]})
        grp, cat = (p.get("group") or ""), (p.get("cat") or "")
        if cat == "ev" and len(grp) == 2 and grp[0] in "fd" and grp[1].isdigit():
            e["line"] = int(grp[1]); e["unit"] = grp[0].upper()
        elif cat == "pp" and grp in ("pp1", "pp2"):
            e["pp"] = int(grp[2])
        elif grp == "g" or cat == "g":
            e["goalie"] = True
        if p.get("inj"):
            e["status"] = "dtd" if p["inj"] == "dtd" else "out"
        if p.get("gtd"):
            e["gtd"] = True
    return info


# ---------------------------------------------------------------- games view: records, team ranks, starting goalies
GOALIE_STATS = "https://api.nhle.com/stats/rest/en/goalie/summary"
RANK_K = 10.0   # games of last season's rate blended into this season's goals for/against when ranking


def standings_on(day):
    j = _get(f"{WEB}/standings/{day}") or {}
    return [{"t": t["teamAbbrev"]["default"], "gp": t.get("gamesPlayed", 0), "w": t.get("wins", 0), "l": t.get("losses", 0),
             "otl": t.get("otLosses", 0), "pts": t.get("points", 0), "gf": t.get("goalFor", 0), "ga": t.get("goalAgainst", 0),
             "l10": [t.get("l10Wins", 0), t.get("l10Losses", 0), t.get("l10OtLosses", 0)],
             "streak": f'{t.get("streakCode") or ""}{t.get("streakCount") or ""}'} for t in j.get("standings", [])]


def team_table(now_rows, last_rows):
    """Records plus offense (goals for/game) and defense (goals against/game) ranks, blended with last season early on."""
    last = {r["t"]: r for r in last_rows}
    lg_gf = sum(r["gf"] for r in last_rows) / max(1, sum(r["gp"] for r in last_rows)) if last_rows else 3.0
    out = {}
    for r in now_rows:
        lr = last.get(r["t"])
        lgf = lr["gf"] / lr["gp"] if lr and lr["gp"] else lg_gf
        lga = lr["ga"] / lr["gp"] if lr and lr["gp"] else lg_gf
        out[r["t"]] = {**r, "gfpg": round((r["gf"] + RANK_K * lgf) / (r["gp"] + RANK_K), 2),
                       "gapg": round((r["ga"] + RANK_K * lga) / (r["gp"] + RANK_K), 2),
                       "last": {k: lr[k] for k in ("gp", "w", "l", "otl", "pts", "gf", "ga")} if lr else None}
    for key, rk, rev in (("gfpg", "offRank", True), ("gapg", "defRank", False)):
        order = sorted(out, key=lambda t: out[t][key], reverse=rev)
        for i, t in enumerate(order):
            out[t][rk] = i + 1
    return out


TEAM_PP = "https://api.nhle.com/stats/rest/en/team/powerplay"
TEAM_PK = "https://api.nhle.com/stats/rest/en/team/penaltykill"
ST_K = 30.0     # power-play chances of last season's rate blended into this season's power-play and penalty-kill rates


def special_teams(season):
    """{team key: [pp goals, pp chances, pp goals against, times shorthanded]} for one regular season."""
    q = {"isAggregate": "false", "isGame": "false", "start": 0, "limit": -1, "cayenneExp": f"seasonId={season} and gameTypeId=2"}
    key = lambda name: (norm_name(name).split() or [""])[-1]
    out = {}
    for r in (_get(TEAM_PP, q) or {}).get("data", []):
        out[key(r["teamFullName"])] = [r.get("powerPlayGoalsFor") or 0, r.get("ppOpportunities") or 0, 0, 0]
    for r in (_get(TEAM_PK, q) or {}).get("data", []):
        o = out.setdefault(key(r["teamFullName"]), [0, 0, 0, 0])
        o[2], o[3] = r.get("ppGoalsAgainst") or 0, r.get("timesShorthanded") or 0
    return out


def add_special_teams(tbl, names, cur, last):
    """Adds power-play % and penalty-kill % (blended with last season early on) and their ranks to the team table."""
    key = lambda name: (norm_name(name).split() or [""])[-1]
    tot = [sum(v[i] for v in last.values()) for i in range(4)] if last else [0, 0, 0, 0]
    lg_pp = tot[0] / tot[1] if tot[1] else 0.21
    lg_pk = tot[2] / tot[3] if tot[3] else 0.21
    for abbr, row in tbl.items():
        k = key(names.get(abbr, abbr))
        c, l = cur.get(k), last.get(k)
        if not c and not l:
            continue
        c = c or [0, 0, 0, 0]
        lpp = l[0] / l[1] if l and l[1] else lg_pp
        lpk = l[2] / l[3] if l and l[3] else lg_pk
        row["pp"] = round(100 * (c[0] + ST_K * lpp) / (c[1] + ST_K), 1)
        row["pk"] = round(100 * (1 - (c[2] + ST_K * lpk) / (c[3] + ST_K)), 1)
        row["ppNow"] = [c[0], c[1]]
        row["pkNow"] = [c[3] - c[2], c[3]]
    for k_, rk in (("pp", "ppRank"), ("pk", "pkRank")):
        order = sorted((t for t in tbl if k_ in tbl[t]), key=lambda t: tbl[t][k_], reverse=True)
        for i, t in enumerate(order):
            tbl[t][rk] = i + 1
    return tbl


def goalie_stats(season):
    exp = f"seasonId={season} and gameTypeId=2"
    j = _get(GOALIE_STATS, {"isAggregate": "false", "isGame": "false", "start": 0, "limit": -1, "cayenneExp": exp}) or {}
    return {norm_name(g["goalieFullName"]): {"gp": g.get("gamesPlayed", 0), "w": g.get("wins", 0), "l": g.get("losses", 0),
            "otl": g.get("otLosses", 0), "sv": g.get("savePct"), "gaa": g.get("goalsAgainstAverage"), "so": g.get("shutouts", 0)}
            for g in j.get("data", [])}


def dfo_starting_goalies(day):
    """[{home, away (team names), hg, ag}] from DailyFaceoff's starting goalies page for one date."""
    nd = _dfo_page(f"/starting-goalies/{day}") or {}
    pp = nd.get("props", {}).get("pageProps", {})

    def g(x, p):
        return {"name": x.get(p + "GoalieName"), "status": x.get(p + "NewsStrengthName"), "src": x.get(p + "NewsSourceName"),
                "at": x.get(p + "NewsCreatedAt"), "dfoHs": x.get(p + "GoalieHeadshotUrl")}
    return [{"home": x.get("homeTeamName"), "away": x.get("awayTeamName"), "hg": g(x, "home"), "ag": g(x, "away")} for x in pp.get("data", [])]


def attach_goalies(games, names, by_day, g_cur, g_last, roster_goalies=None):
    """{gid: {abbr: goalie}} matching DailyFaceoff games to NHL games by date and team names."""
    def same(a, b):
        a, b = norm_name(a), norm_name(b)
        return a == b or (a.split() and b.split() and a.split()[-1] == b.split()[-1])
    out = {}
    for g in games:
        for x in by_day.get(g["day"], []):
            if same(x["home"], names.get(g["home"], g["home"])) and same(x["away"], names.get(g["away"], g["away"])):
                entry = {}
                for side, abbr in (("hg", g["home"]), ("ag", g["away"])):
                    gl = dict(x[side] or {})
                    if not gl.get("name"):
                        continue
                    k = norm_name(gl["name"])
                    gl["cur"], gl["last"] = g_cur.get(k), g_last.get(k)
                    rg = (roster_goalies or {}).get((abbr, k))
                    if not rg:   # same last name + first initial (Sam/Samuel etc.)
                        parts = k.split()
                        rg = next((v for (t, nk), v in (roster_goalies or {}).items()
                                   if t == abbr and parts and nk.split()[-1] == parts[-1] and nk[0] == parts[0][0]), None)
                    gl["hs"] = (rg or {}).get("hs") or gl.pop("dfoHs", None) or ""
                    gl.pop("dfoHs", None)
                    entry[abbr] = gl
                out[g["id"]] = entry
                break
    return out

# ---------------------------------------------------------------- odds
def fetch_odds(api_key, book, games, names, only_date=None):
    """{gid: {norm player: {stat: [[line, over, under], ...]}}}, message. Every line Hard Rock posts. About 1 credit per game."""
    r = requests.get(f"{ODDS_BASE}/events", params={"apiKey": api_key}, timeout=30)
    if r.status_code == 401:
        return {}, "Odds API key was rejected."
    r.raise_for_status()
    now = datetime.now(ET)
    idx = {}
    for g in games:
        idx[(norm_name(names.get(g["home"], g["home"])), norm_name(names.get(g["away"], g["away"])), g["day"])] = g["id"]

    def find(home, away, day):
        h, a = norm_name(home), norm_name(away)
        for (gh, ga, gd), gid in idx.items():
            if gd == day and (gh == h or h.endswith(gh.split()[-1])) and (ga == a or a.endswith(ga.split()[-1])):
                return gid
        return None

    out, fetched, remaining, first_ev, used = {}, 0, None, None, set()
    order = list(dict.fromkeys([book, "hardrockbet", "hardrockbet_fl", "hardrockbet_az", "hardrockbet_oh"]))
    for ev in r.json():
        start = datetime.fromisoformat(ev["commence_time"].replace("Z", "+00:00")).astimezone(ET)
        if only_date and start.date().isoformat() != only_date:
            continue
        if not only_date and (start - now).days > 2:
            continue
        gid = find(ev["home_team"], ev["away_team"], start.date().isoformat())
        if not gid:
            continue
        first_ev = first_ev or ev["id"]
        rr = requests.get(f"{ODDS_BASE}/events/{ev['id']}/odds", timeout=30, params={
            "apiKey": api_key, "bookmakers": ",".join(order), "markets": ",".join(MARKETS), "oddsFormat": "american"})
        remaining = rr.headers.get("x-requests-remaining", remaining)
        if rr.status_code == 429:
            break
        if rr.status_code != 200:
            continue
        fetched += 1
        by_book = {}
        for bm in rr.json().get("bookmakers", []):
            entry = by_book.setdefault(bm.get("key"), {})
            for m in bm.get("markets", []):
                stat = MARKETS.get(m.get("key"))
                for o in m.get("outcomes", []):
                    player, side, price, pt = o.get("description"), o.get("name"), o.get("price"), o.get("point")
                    if not stat or not player or price is None or pt is None or side not in ("Over", "Under"):
                        continue
                    lines = entry.setdefault(norm_name(player), {}).setdefault(stat, [])
                    slot = next((x for x in lines if x[0] == float(pt)), None)
                    if slot is None:
                        slot = [float(pt), None, None]; lines.append(slot)
                    slot[1 if side == "Over" else 2] = int(price)
        entry = {}
        for k in order:   # selected Hard Rock feed first, then the other Hard Rock feeds
            for player, v in by_book.get(k, {}).items():
                for stat, lines in v.items():
                    if lines:
                        entry.setdefault(player, {}).setdefault(stat, lines)
        used.update(k for k, v in by_book.items() if v)
        if entry:
            out[gid] = entry
    msg = f"NHL: Hard Rock player points/shots for {len(out)} of {fetched} games checked" + (f" (from {', '.join(sorted(used))})" if used else "")
    if fetched and not out and first_ev:
        # Hard Rock came back empty: which US books do list NHL player points for one game? (about 2 credits)
        try:
            rr = requests.get(f"{ODDS_BASE}/events/{first_ev}/odds", timeout=30, params={
                "apiKey": api_key, "regions": "us,us2", "markets": "player_points", "oddsFormat": "american"})
            if rr.status_code == 200:
                have = [b["title"] for b in rr.json().get("bookmakers", [])
                        if any(m.get("key") == "player_points" and m.get("outcomes") for m in b.get("markets", []))]
                msg += (f"; Hard Rock isn't offering NHL player points through The Odds API right now (available from: {', '.join(have)})"
                        if have else "; no US book has posted NHL player points yet, try closer to puck drop")
        except requests.RequestException:
            pass
    if remaining is not None:
        msg += f"; {remaining} credits left"
    return out, msg + "."


def fetch_game_lines(api_key, book, games, names):
    """Hard Rock moneyline, puck line and total for every listed NHL game: ONE request (~3 credits for 3 markets).
    Returns ({gid: {"ml": {team: price}, "pl": {team: [point, price]}, "tot": [point, over, under], "book": key}}, message)."""
    order = list(dict.fromkeys([book, "hardrockbet", "hardrockbet_fl", "hardrockbet_az", "hardrockbet_oh"]))
    r = requests.get(f"{ODDS_BASE}/odds", timeout=30, params={
        "apiKey": api_key, "bookmakers": ",".join(order), "markets": "h2h,spreads,totals", "oddsFormat": "american"})
    if r.status_code == 401:
        return {}, "Odds API key was rejected."
    r.raise_for_status()
    abbr = {norm_name(names.get(t, t)): t for g in games for t in (g["home"], g["away"])}

    def team_of(full):
        n = norm_name(full)
        if n in abbr:
            return abbr[n]
        return next((t for k, t in abbr.items() if k.split()[-1] == n.split()[-1]), None)

    out = {}
    for ev in r.json():
        day = datetime.fromisoformat(ev["commence_time"].replace("Z", "+00:00")).astimezone(ET).date().isoformat()
        h, a = team_of(ev["home_team"]), team_of(ev["away_team"])
        g = next((g for g in games if g["day"] == day and g["home"] == h and g["away"] == a), None)
        if not g:
            continue
        by_book = {bm["key"]: bm for bm in ev.get("bookmakers", [])}
        e = {}
        for k in order:
            bm = by_book.get(k)
            if not bm:
                continue
            for m in bm.get("markets", []):
                oc = m.get("outcomes", [])
                if m["key"] == "h2h" and "ml" not in e:
                    e["ml"] = {team_of(o["name"]): o["price"] for o in oc if team_of(o["name"])}
                elif m["key"] == "spreads" and "pl" not in e:
                    e["pl"] = {team_of(o["name"]): [o.get("point"), o["price"]] for o in oc if team_of(o["name"])}
                elif m["key"] == "totals" and "tot" not in e:
                    ov = next((o for o in oc if o["name"] == "Over"), None); un = next((o for o in oc if o["name"] == "Under"), None)
                    if ov or un:
                        e["tot"] = [(ov or un).get("point"), ov and ov["price"], un and un["price"]]
            e.setdefault("book", k)
        if len(e) > 1:
            out[g["id"]] = e
    left = r.headers.get("x-requests-remaining")
    return out, f"NHL: Hard Rock game lines for {len(out)} games" + (f"; {left} credits left" if left else "") + "."


def _pois_cdf(k, lam):
    term = cdf = math.exp(-lam)
    for i in range(1, k + 1):
        term *= lam / i; cdf += term
    return cdf


def _no_vig(a, b):
    ia = 100 / (a + 100) if a > 0 else -a / (-a + 100)
    ib = 100 / (b + 100) if b > 0 else -b / (-b + 100)
    return ia / (ia + ib)


def implied_team_goals(gl, home, away):
    """(home goals, away goals) implied by Hard Rock's total and moneyline, or None.
    Total: the Poisson mean whose chance of going over the line matches the no-vig Over price.
    Split: the share of that total that makes the home team's win chance match the no-vig moneyline
    (regulation ties count half, since overtime is close to a coin flip)."""
    tot, ml = gl.get("tot"), gl.get("ml") or {}
    if not tot or tot[0] is None or tot[1] is None or tot[2] is None or ml.get(home) is None or ml.get(away) is None:
        return None
    line, p_over, p_home = float(tot[0]), _no_vig(tot[1], tot[2]), _no_vig(ml[home], ml[away])
    k = int(math.floor(line))
    lo, hi = 2.0, 12.0
    for _ in range(60):
        mid = (lo + hi) / 2
        po = 1 - _pois_cdf(k, mid)
        if abs(line - k) < 1e-9:            # whole-number total: a push is possible, compare over vs over+under
            po = po / (1 - (_pois_cdf(k, mid) - _pois_cdf(k - 1, mid)))
        lo, hi = (mid, hi) if po < p_over else (lo, mid)
    total = (lo + hi) / 2

    def home_win(share):
        lh, la = total * share, total * (1 - share)
        ph = [math.exp(-lh)]; pa = [math.exp(-la)]
        for i in range(1, 16):
            ph.append(ph[-1] * lh / i); pa.append(pa[-1] * la / i)
        win = sum(ph[i] * sum(pa[:i]) for i in range(16))
        tie = sum(ph[i] * pa[i] for i in range(16))
        return win + tie / 2
    lo, hi = 0.2, 0.8
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if home_win(mid) < p_home else (lo, mid)
    share = (lo + hi) / 2
    return total * share, total * (1 - share)


def model_team_goals(st, team, opp, home):
    """What the model's team ratings expect this team to score tonight (for comparing with the market)."""
    p, tm = st.p, st.tm
    W = sum(t["w"] for t in tm.values()) or 1
    lg = sum(t["gf"] for t in tm.values()) / W or 3.0
    K = p["TEAM_K"]
    own, o = tm.get(team), tm.get(opp)
    off = (own["gf"] + K * lg) / (own["w"] + K) / lg if own else 1.0
    dfn = (o["ga"] + K * lg) / (o["w"] + K) / lg if o else 1.0
    return lg * off * dfn * (p["HOME"] if home else 1 / p["HOME"])


def apply_market(st, games, proj, game_lines):
    """Nudge upcoming points projections toward the team goals Hard Rock's game lines imply."""
    p = st.p
    for g in games:
        gl, rows = game_lines.get(str(g["id"])), proj.get(g["id"]) or proj.get(str(g["id"]))
        if not gl or not rows or any(r.get("res") for r in rows):
            continue
        imp = implied_team_goals(gl, g["home"], g["away"])
        if not imp:
            continue
        fac = {}
        for team, opp, home, goals in ((g["home"], g["away"], True, imp[0]), (g["away"], g["home"], False, imp[1])):
            f = (goals / model_team_goals(st, team, opp, home)) ** p["MKT_W"]
            fac[team] = max(1 - p["MKT_CAP"], min(1 + p["MKT_CAP"], f))
        g["implied"] = {g["home"]: round(imp[0], 2), g["away"]: round(imp[1], 2)}
        for r in rows:
            f = fac.get(r["team"], 1.0)
            r["pts"] = round(r["pts"] * f, 4)
            r["mkt"] = round(f, 3)


# ---------------------------------------------------------------- build
def _replay(st, rows, splits, snap_from, snaps, att=None):
    """Feed rows (sorted by date) into the model; record pre-game projections for games on/after snap_from."""
    by_game = {}
    for r in rows:
        by_game.setdefault((r[1], r[0]), []).append(r)
    month = None
    for (day, gid), grp in sorted(by_game.items()):
        if day[:7] != month and len(st.pl) > 300:
            st.fit_priors(); month = day[:7]
        lmq = _game_linemates(st, grp, splits)
        if snaps is not None and day >= snap_from:
            for r in grp:
                pr = st.project(r[2], r[7], r[5], r[6] == "H", None, r[4], st.b2b(r[4], day), False, lmq.get(r[2]))
                snaps.setdefault(str(gid), []).append((r, pr, _ctx(st, r[2], r[4])))
        gf, sf, ppt, sht = {}, {}, {}, {}
        for r in grp:
            gf[r[4]] = gf.get(r[4], 0) + r[8]; sf[r[4]] = sf.get(r[4], 0) + r[11]
            ev, pp, sh = splits.get((r[0], r[2])) or (0, 0, 0)
            ppt[r[4]] = max(ppt.get(r[4], 0), pp); sht[r[4]] = max(sht.get(r[4], 0), sh)
        venue = next((r[4] for r in grp if r[6] == "H"), None)
        if venue:
            st.update_rink(venue, sf)
        for t in gf:
            st.update_team(t, gf[t], sum(v for k, v in gf.items() if k != t), day, sf[t], sum(v for k, v in sf.items() if k != t),
                           ppt[t], sht[t])
        rkf = st.rink(venue) if venue else 1.0
        for r in grp:
            st.update_player(r, splits.get((r[0], r[2])), lmq.get(r[2]), rkf, (att or {}).get((r[0], r[2])))


def _linemate_q(st, members):
    """{pid: average EV points/60 of his linemates}. members = [(pid, pos, team, line)]."""
    q = {pid: st.ev_rate(pid, pos) for pid, pos, team, line in members}
    groups = {}
    for pid, pos, team, line in members:
        if line:
            groups.setdefault((team, grp_of(pos), line), []).append(pid)
    out = {}
    for pid, pos, team, line in members:
        if not line:
            continue
        g = grp_of(pos)
        mates = [q[x] for x in groups[(team, g, line)] if x != pid]
        if g == "D":     # a pair plays behind the matching forward line
            mates += [q[x] for x in groups.get((team, "F", line), [])]
        if mates:
            out[pid] = sum(mates) / len(mates)
    return out


def _game_linemates(st, grp, splits):
    """Past game: lines rebuilt from even-strength ice-time ranks (the NHL doesn't publish historical line combos)."""
    if not st.fit:
        return {}
    members, by_team = [], {}
    for r in grp:
        by_team.setdefault(r[4], []).append(r)
    for team, rs in by_team.items():
        ev = {r[2]: (splits.get((r[0], r[2])) or (r[13], 0, 0))[0] for r in rs}
        F = sorted((r for r in rs if r[7] != "D"), key=lambda r: -ev[r[2]])
        D = sorted((r for r in rs if r[7] == "D"), key=lambda r: -ev[r[2]])
        members += [(r[2], r[7], team, min(4, i // 3 + 1)) for i, r in enumerate(F)]
        members += [(r[2], r[7], team, min(3, i // 2 + 1)) for i, r in enumerate(D)]
    return _linemate_q(st, members)


def _ctx(st, pid, team):
    """Recent form and role context as of now (call before the game is fed in)."""
    s = st.pl.get(pid) or {}
    rec = s.get("recent", [])
    t_dates = set((st.tm.get(team) or {}).get("dates", [])[-5:])
    return {"n": s.get("season_n", 0), "career": s.get("n", 0),
            "l10": [sum(x[1] for x in rec), sum(x[2] for x in rec), len(rec)],
            "s10": [x[5] for x in rec if len(x) > 5],
            "dressed": [sum(1 for x in rec if x[0] in t_dates), len(t_dates)] if t_dates else None}


def _row(pid, name, pos, team, opp, home, pr, hs, ctx, result=None, lu=None):
    row = {"pid": pid, "name": name, "pos": pos, "team": team, "opp": opp, "home": home, "hs": hs,
           "toi": round(pr["toi"], 1), "toi0": round(pr["toi0"], 1), "pp_m": round(pr["pp"], 1),
           "pts": round(pr["pts"], 4), "p60": round(pr["p60"], 2), "env": round(pr["env"], 3),
           "sog": round(pr["sog"], 4), "s60": round(pr["s60"], 2), "senv": round(pr["senv"], 3), "b2b": pr["b2b"],
           "lmf": round(pr["lmf"], 3), "rink": round(pr["rink"], 3), "ppf": round(pr["ppf"], 3),
           **ctx, "res": result}
    if lu is not None:
        row["lu"] = lu
    return row


def build(odds_key=None, book="hardrockbet_fl", odds_date=None, fetch_odds_now=True, today=None, dfo=None):
    today = today or datetime.now(ET).date()
    season = season_id(today)
    y0 = int(season[:4])
    prev, prev2 = f"{y0 - 1}{y0}", f"{y0 - 2}{y0 - 1}"
    print("NHL: downloading skater game logs and ice-time splits…")
    prev2_rows, prev_rows, cur_rows = skater_games(prev2, today), skater_games(prev, today), skater_games(season, today)
    splits = {}
    for s_ in (prev2, prev, season):
        splits.update(toi_splits(s_, today))
    att = {}
    for s_ in (prev2, prev, season):
        att.update(shot_attempts(s_, today))
    typ = slot_minutes(prev_rows + cur_rows, splits)
    first, last = today - timedelta(days=PAST_DAYS), today + timedelta(days=AHEAD_DAYS)
    if odds_date:
        od = date.fromisoformat(odds_date)
        first, last = min(first, od), max(last, od)
    print("NHL: schedule and rosters…")
    games = schedule(first, last)
    roster_goalies = {}
    roster = rosters(season, roster_goalies)

    st = State()
    _replay(st, prev2_rows, splits, None, None, att)   # two seasons back, so players who missed last season keep their history
    st.new_season()
    _replay(st, prev_rows, splits, None, None, att)
    st.new_season()
    snaps = {}
    _replay(st, cur_rows, splits, first.isoformat(), snaps, att)
    st.fit_priors()

    names = {}
    for g in games:
        names.update(g.pop("_names"))
    upcoming = [g for g in games if g["id"] not in snaps and g["state"] in ("FUT", "PRE", "LIVE", "CRIT") and g["day"] >= today.isoformat()]
    status = []
    if dfo is None:
        print("NHL: DailyFaceoff line combinations…")
        teams = sorted({t for g in upcoming for t in (g["home"], g["away"])})
        dfo, msg = fetch_dfo(teams) if teams else ({}, "")
        if msg:
            status.append(msg)
    log_dfo(today.isoformat(), dfo)
    lineups = {t: lineup_map(c) for t, c in dfo.items()}

    team_days = {(t, g["day"]) for g in games for t in (g["home"], g["away"])}

    def is_b2b(team, day):
        return (team, (date.fromisoformat(day) - timedelta(days=1)).isoformat()) in team_days or st.b2b(team, day)

    proj = {}
    for g in games:
        gid = g["id"]
        if gid in snaps:   # finished: pre-game projection for everyone who dressed, plus the result
            proj[gid] = [_row(r[2], r[3], r[7], r[4], r[5], r[6] == "H", pr, (roster.get(r[2]) or {}).get("hs", ""), ctx,
                              {"pts": r[10], "g": r[8], "a": r[9], "sog": r[11], "toi": round(r[13] / 60, 1)})
                         for r, pr, ctx in snaps[gid]]
        elif g in upcoming:
            rows, cands = [], []
            for pid, info in roster.items():
                if info["team"] not in (g["home"], g["away"]):
                    continue
                home = info["team"] == g["home"]
                opp = g["away"] if home else g["home"]
                s = st.pl.get(pid)
                name = (s or {}).get("name") or info["name"]
                lu, slot_typ, top = None, None, False
                team_lu = lineups.get(info["team"])
                if team_lu is not None:
                    e = find_in_lineup(team_lu, name, info["name"])
                    if e is None:
                        lu = {"line": None, "pp": 0, "status": "scratch"}
                    else:
                        lu = {"line": e["line"], "pp": e["pp"], "status": e["status"], "gtd": e["gtd"]}
                        if e["line"]:
                            slot_typ = typ.get((grp_of(info["pos"]), e["line"], e["pp"]))
                            top = (e["line"] <= (1 if info["pos"] == "D" else 2)) or e["pp"] == 1
                        elif not e["status"]:
                            lu["status"] = "scratch"
                cands.append((pid, info, name, home, opp, lu, slot_typ, top))
            # tonight's linemates from DailyFaceoff (players listed on a line and not injured)
            lmq = _linemate_q(st, [(c[0], c[1]["pos"], c[1]["team"], c[5]["line"]) for c in cands
                                   if c[5] and c[5].get("line") and c[5].get("status") not in ("out", "scratch")])
            for pid, info, name, home, opp, lu, slot_typ, top in cands:
                pr = st.project(pid, info["pos"], opp, home, slot_typ, info["team"], is_b2b(info["team"], g["day"]), top, lmq.get(pid))
                rows.append(_row(pid, name, info["pos"], info["team"], opp, home, pr, info["hs"], _ctx(st, pid, info["team"]), None, lu))
            proj[gid] = rows
            src = {t: (dfo.get(t) or {}).get("source") for t in (g["home"], g["away"])}
            g["lines"] = {t: {"source": s_, "kind": lines_kind(s_), "updatedAt": (dfo.get(t) or {}).get("updatedAt")}
                          for t, s_ in src.items() if s_}

    cache_path = CACHE / f"nhl_odds_{season}_{book}.json"
    try:
        odds_cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    except ValueError:
        odds_cache = {}
    if odds_key and fetch_odds_now:
        try:
            got, msg = fetch_odds(odds_key, book, upcoming, names, odds_date)
            stamp = datetime.now(ET).isoformat()
            for gid, e in got.items():
                odds_cache[gid] = {"fetched": stamp, "props": e}
            cache_path.write_text(json.dumps(odds_cache))
        except requests.RequestException as e:
            msg = f"NHL: couldn't reach The Odds API ({e}); kept earlier odds."
        status.append(msg)
        print(msg)
    gl_path = CACHE / f"nhl_gamelines_{season}.json"
    try:
        game_lines = json.loads(gl_path.read_text()) if gl_path.exists() else {}
    except ValueError:
        game_lines = {}
    if odds_key and fetch_odds_now:
        try:
            got, msg = fetch_game_lines(odds_key, book, [g for g in games if g["day"] >= today.isoformat()], names)
            stamp = datetime.now(ET).isoformat()
            for gid, e in got.items():
                game_lines[str(gid)] = {**e, "fetched": stamp}
            gl_path.write_text(json.dumps(game_lines))
            status.append(msg)
        except requests.RequestException as e:
            status.append(f"NHL game lines unavailable ({e}).")
    game_lines = {gid: v for gid, v in game_lines.items() if any(str(g["id"]) == gid for g in games)}
    apply_market(st, [g for g in games if g in upcoming], proj, game_lines)
    odds, odds_times = {}, {}
    for gid, rows in proj.items():
        c = odds_cache.get(gid)
        if not c:
            continue
        odds_times[gid] = c["fetched"]
        for r in rows:
            o = c["props"].get(norm_name(r["name"]))
            if o:
                odds.setdefault(gid, {})[str(r["pid"])] = o

    print("NHL: standings, goalie stats and starting goalies…")
    teams_tbl, goalies = {}, {}
    try:
        teams_tbl = team_table(standings_on(today.isoformat()), standings_on(f"{y0}-05-01"))
    except Exception as e:  # standings are nice-to-have
        status.append(f"NHL standings unavailable ({e}).")
    try:
        if teams_tbl:
            add_special_teams(teams_tbl, names, special_teams(season), special_teams(prev))
    except Exception as e:  # power-play and penalty-kill ranks are nice-to-have
        status.append(f"NHL power-play and penalty-kill ranks unavailable ({e}).")
    try:
        g_cur, g_last = goalie_stats(season), goalie_stats(prev)
        days = sorted({g["day"] for g in upcoming})[:3]
        by_day = {}
        for d in days:
            try:
                by_day[d] = dfo_starting_goalies(d)
            except (requests.RequestException, ValueError):
                pass
        goalies = attach_goalies([g for g in games if g["day"] in by_day], names, by_day, g_cur, g_last, roster_goalies)
    except Exception as e:
        status.append(f"Starting goalies unavailable ({e}).")
    logos = {t: [names.get(t, t), f"https://assets.nhle.com/logos/nhl/svg/{t}_dark.svg"] for t in set(names) | set(TEAMS)}
    return {"season": season, "games": games, "teams": logos, "proj": proj, "odds": odds, "oddsTimes": odds_times,
            "teamStats": teams_tbl, "goalies": goalies, "gameLines": game_lines,
            "status": " ".join(status), "book": book if odds_cache else None, "hasLines": bool(dfo),
            "model": {"backtest": "2025-26 regular season, walk-forward", "logloss": 0.5879, "sogLogloss": 0.438, "sogBaseline": 0.509},
            "generated": datetime.now(ET).strftime("%b %d, %Y at %I:%M %p ET").replace(" 0", " ")}
