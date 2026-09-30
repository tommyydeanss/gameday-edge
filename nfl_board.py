#!/usr/bin/env python3
"""
nfl_board.py - Build the NFL Game Day Board with player prop stats, then open it.

Easiest: run it as your one-stop board (double-click "Start NFL Board" or run):

    python nfl_board.py --serve          # opens http://localhost:8765 with Refresh + saved key

Or build a standalone file whenever you want fresh numbers:

    pip install requests
    python nfl_board.py                  # current season, opens GameDayBoard.html
    python nfl_board.py --season 2025    # a past season
    python nfl_board.py --no-open        # just write the file

Sportsbook odds (optional): get a free key at https://the-odds-api.com, then
    python nfl_board.py --odds-key YOUR_KEY           # Hard Rock Bet (FL) by default
or set it once:  export ODDS_API_KEY=YOUR_KEY   (Windows: setx ODDS_API_KEY YOUR_KEY)

Data: nflverse (github.com/nflverse), free and open. Schedules, scores, lines and
weather come from nfldata/games.csv; weekly player box scores come from the
nflverse-data "stats_player" release. The player-stats file can't be read by a
web page directly, which is why this script downloads everything and bakes it
into one HTML file that works offline.
"""

import argparse
import csv
import gzip
import io
import json
import math
import os
from collections import defaultdict
import webbrowser
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import requests

ET = ZoneInfo("America/New_York")
try:
    import nhl_props  # NHL player points tab (nhl_props.py sits next to this file)
except ImportError:
    nhl_props = None
GAMES_URL = "https://raw.githubusercontent.com/nflverse/nfldata/master/data/games.csv"
TEAMS_URL = "https://raw.githubusercontent.com/nflverse/nfldata/master/data/teams.csv"
RELEASES = "https://github.com/nflverse/nflverse-data/releases/download/"
STATS_URL = RELEASES + "stats_player/stats_player_week_{season}.csv"
PBP_URL = RELEASES + "pbp/play_by_play_{season}.csv.gz"
INJ_URL = RELEASES + "injuries/injuries_{season}.csv"
SNAPS_URL = RELEASES + "snap_counts/snap_counts_{season}.csv"
FORECAST_URL = "https://api.open-meteo.com/v1/forecast"  # free, no key

# Stadium coordinates for weather forecasts (nflverse stadium ids)
STADIUMS = {
    "ATL97": (33.755, -84.401), "BAL00": (39.278, -76.623), "BOS00": (42.091, -71.264), "BUF00": (42.774, -78.787),
    "CAR00": (35.226, -80.853), "CHI98": (41.862, -87.617), "CIN00": (39.095, -84.516), "CLE00": (41.506, -81.700),
    "DAL00": (32.748, -97.093), "DEN00": (39.744, -105.020), "DET00": (42.340, -83.046), "GNB00": (44.501, -88.062),
    "HOU00": (29.685, -95.411), "IND00": (39.760, -86.164), "JAX00": (30.324, -81.637), "KAN00": (39.049, -94.484),
    "LAX01": (33.953, -118.339), "LON00": (51.556, -0.280), "LON02": (51.604, -0.066), "MAD01": (40.453, -3.688),
    "MEL00": (-37.820, 144.983), "MEX00": (19.303, -99.150), "MIA00": (25.958, -80.239), "MIN01": (44.974, -93.258),
    "MUN01": (48.219, 11.625), "NAS00": (36.166, -86.771), "NOR00": (29.951, -90.081), "NYC01": (40.814, -74.074),
    "PAR00": (48.924, 2.360), "PHI00": (39.901, -75.168), "PHO00": (33.528, -112.263), "PIT00": (40.447, -80.016),
    "RIO00": (-22.912, -43.230), "SEA00": (47.595, -122.332), "SFO01": (37.403, -121.970), "TAM00": (27.976, -82.503),
    "VEG00": (36.091, -115.184), "WAS00": (38.908, -76.864),
}


def covered(roof):
    """Domes and closed roofs block weather; retractable roofs with no listed status are assumed closed."""
    return roof not in ("outdoors", "open")


def fetch_forecasts(games_raw, days_ahead=10):
    """Kickoff-hour temperature, wind and rain chance for upcoming outdoor games (Open-Meteo)."""
    out = {}
    today = datetime.now(ET).date()
    for g in games_raw:
        if g["home_score"] or covered(g["roof"]) or g["stadium_id"] not in STADIUMS:
            continue
        try:
            day = datetime.strptime(g["gameday"], "%Y-%m-%d").date()
        except ValueError:
            continue
        if not (0 <= (day - today).days <= days_ahead):
            continue
        lat, lon = STADIUMS[g["stadium_id"]]
        try:
            r = requests.get(FORECAST_URL, timeout=15, params={
                "latitude": lat, "longitude": lon, "hourly": "temperature_2m,wind_speed_10m,precipitation_probability",
                "temperature_unit": "fahrenheit", "wind_speed_unit": "mph", "timezone": "America/New_York",
                "start_date": g["gameday"], "end_date": g["gameday"]})
            r.raise_for_status()
            h = r.json().get("hourly", {})
            stamp = f"{g['gameday']}T{g['gametime'][:2]}:00"
            i = h.get("time", []).index(stamp)
            out[g["game_id"]] = {"temp": round(h["temperature_2m"][i]), "wind": round(h["wind_speed_10m"][i]),
                                 "pop": h.get("precipitation_probability", [None] * (i + 1))[i]}
        except (requests.RequestException, ValueError, KeyError, IndexError, TypeError):
            continue
    return out
PLAYERS_URL = RELEASES + "players/players.csv"
CACHE = Path(__file__).resolve().parent / ".nfl_cache"  # finished seasons never change

POS_MAP = {"QB": "QB", "RB": "RB", "FB": "RB", "WR": "WR", "TE": "TE"}
# Order matters: the page reads these by index.
STAT_COLS = ["completions", "attempts", "passing_yards", "passing_tds", "passing_interceptions",
             "carries", "rushing_yards", "rushing_tds",
             "targets", "receptions", "receiving_yards", "receiving_tds"]


def get_bytes(url, cache_name=None):
    """Download a file; finished-season files are cached next to this script."""
    if cache_name and (CACHE / cache_name).exists():
        return (CACHE / cache_name).read_bytes()
    resp = requests.get(url, timeout=180)
    if resp.status_code == 404:
        return None
    resp.raise_for_status()
    if cache_name:
        CACHE.mkdir(exist_ok=True)
        (CACHE / cache_name).write_bytes(resp.content)
    return resp.content


def get_csv(url):
    resp = requests.get(url, timeout=60)
    if resp.status_code == 404:
        return None
    resp.raise_for_status()
    return list(csv.DictReader(io.StringIO(resp.text)))


def to_int(v):
    try:
        return int(round(float(v)))
    except (TypeError, ValueError):
        return 0


def to_num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


# ---------------------------------------------------------------------------
# Anytime-touchdown model
#
# For a player on team T facing opponent O:
#   1. Team TDs      = offensive TDs per Vegas-implied point x T's implied points
#                      (falls back to recent scoring when there's no line)
#   2. Rush/pass mix = T's share of expected TDs on runs vs targets, shrunk to league
#   3. Player share  = player's share of T's expected TDs (xTD) on carries and targets,
#                      where every carry/target is valued by the league TD rate from that
#                      spot on the field, blended with plain carry/target share
#   4. P(anytime TD) = 1 - exp(-lambda)
# Only games before the prediction date count. The last three seasons count at reduced weight
# (35%, 15%, 7% of a current-season game), and a player's older share is adjusted by an age curve
# fitted on 2019-2025 (e.g. running backs 26+ and receivers 28+ tend to lose share each year).
# Players who missed the team's last two games are left out, and the listed starting QB
# replaces the usual starter when they differ.
#
# Backtests (predict each week from earlier weeks only, players who suited up):
#   2024 Brier 0.156 vs 0.169 for position averages; 2025 Brier 0.150 vs 0.164.
#   Adding two more past seasons plus the age curve improved both seasons again, most in
#   weeks 3-6 when current-season samples are small. Counting games with a former team hurt.
#   Removing players listed Out/Doubtful on the official injury report improved log loss a bit
#   more in both seasons.
#   Defense-vs-position TD splits made both seasons slightly worse, so they are shown
#   on the board as context but do not change the probabilities.
# ---------------------------------------------------------------------------
YARD_BUCKETS = [(1, 2), (3, 5), (6, 10), (11, 20), (21, 100)]
PREV_SEASON_WEIGHT = 0.35
# Weight of each earlier season relative to the current one (1 = last season, 2 = two seasons ago, ...)
HISTORY_WEIGHTS = {1: 0.35, 2: 0.15, 3: 0.07}
# Year-over-year change in a player's share of team expected TDs, by position and age at the start of
# the earlier season (ratio of next-season share to this-season share, shrunk toward 1).
# Fitted on 1,462 player-season pairs, 2019-2025; QBs are left flat (too few rushing-TD samples).
AGE_CURVE = {
    "RB": {"24-25": 0.979, "26-27": 0.939, "28-29": 0.935, "30-31": 0.954, "32+": 0.956, "<=23": 1.037},
    "TE": {"24-25": 0.979, "26-27": 1.01, "28-29": 0.956, "30-31": 0.984, "32+": 0.94, "<=23": 1.033},
    "WR": {"24-25": 1.026, "26-27": 0.962, "28-29": 0.902, "30-31": 0.894, "32+": 0.907, "<=23": 1.025},
}
USE_AGING = True
# Games a player played for a previous team count at this fraction (role carries over only partly)
OTHER_TEAM_WEIGHT = 0.0
COACH_W = 1.0      # weight on past seasons for a team with a new head coach (tested 0.5: no gain, so off)
SNAP_ALPHA = 0.5   # how far recent snap share moves a player's projected role


def age_bucket(age):
    return "<=23" if age <= 23 else "24-25" if age <= 25 else "26-27" if age <= 27 else \
        "28-29" if age <= 29 else "30-31" if age <= 31 else "32+"


def age_factor(pos, birth, from_season, to_season):
    """Expected multiplier on a player's share between two seasons, from the fitted age curve."""
    if not USE_AGING or not birth or pos not in AGE_CURVE:
        return 1.0
    by, bm, bd = (int(x) for x in birth.split("-")[:3])
    f = 1.0
    for y in range(from_season, to_season):
        age = y - by - ((9, 1) < (bm, bd))
        f *= AGE_CURVE[pos].get(age_bucket(age), 1.0)
    return f
RECENT_GAMES = 2
# Matchup: each defense's TD tendencies, heavily shrunk. Backtests showed defense splits are mostly
# noise, so they get a light touch (about a point either way) on top of the Vegas matchup.
USE_MATCHUP = True
MATCHUP_K_MIX = 64.0  # games of league-average data mixed into a defense's rush/pass TD split
MATCHUP_K_POS = 64.0  # games of league-average data mixed into a defense's receiving-TD split by position  # backtests: defense-vs-position TD splits added noise, so they stay display-only
# Fitted on the 2024 backtest (players who suit up score a bit more than their share implies,
# because some team TD share sits with players who end up inactive). Checked out of sample on 2025.
CALIBRATION = 1.10
USE_VEGAS = True


def bucket(yl):
    for i, (lo, hi) in enumerate(YARD_BUCKETS):
        if lo <= yl <= hi:
            return i
    return len(YARD_BUCKETS) - 1


def _f(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return 0.0


def read_pbp(fileobj):
    """Yield the handful of fields the model needs from a (gzipped) pbp csv."""
    reader = csv.DictReader(io.TextIOWrapper(gzip.GzipFile(fileobj=fileobj), encoding="utf-8"))
    for p in reader:
        if p["season_type"] != "REG" or p["play_type"] not in ("run", "pass"):
            continue
        if p["two_point_attempt"] == "1" or p["qb_kneel"] == "1" or p["qb_spike"] == "1":
            continue
        yl = _f(p["yardline_100"])
        if yl <= 0:
            continue
        rush = p["rush_attempt"] == "1" and p["rusher_player_id"]
        tgt = p["pass_attempt"] == "1" and p["receiver_player_id"] and p["sack"] != "1"
        if not (rush or tgt):
            continue
        td = (p["rush_touchdown"] == "1" or p["pass_touchdown"] == "1") and p["td_team"] == p["posteam"]
        yield {
            "gid": p["game_id"], "off": p["posteam"], "def": p["defteam"], "yl": int(yl),
            "kind": "rush" if rush else "rec",
            "pid": p["rusher_player_id"] if rush else p["receiver_player_id"],
            "name": p["rusher_player_name"] if rush else p["receiver_player_name"],
            "td": 1 if td and p["td_player_id"] == (p["rusher_player_id"] if rush else p["receiver_player_id"]) else 0,
        }


class TDModel:
    def __init__(self, plays_by_season, games, positions, season, births=None, snaps=None, coaches=None):
        """
        plays_by_season: {season: [play dicts]} for the prior season and the current one
        games: list of game dicts (id, season, day, home, away, hs, as, spread, total)
        positions: {player_id: 'QB'|'RB'|'WR'|'TE'}
        """
        self.season = season
        self.pos = positions
        self.births = births or {}
        self.snaps = snaps or {}
        self.coaches = coaches or {}
        self.games = {g["id"]: g for g in games}
        prior = plays_by_season.get(season - 1, [])

        # League TD rate per carry / per target at each field-position bucket (from last season,
        # or current data if last season is missing).
        base = prior or plays_by_season.get(season, [])
        att, tds = defaultdict(float), defaultdict(float)
        for p in base:
            k = (p["kind"], bucket(p["yl"]))
            att[k] += 1
            tds[k] += p["td"]
        self.rate = {k: (tds[k] + 0.5) / (att[k] + 5) for k in att}

        # Aggregate every team-game and player-game.
        self.team_games = defaultdict(lambda: {"x_rush": 0.0, "x_rec": 0.0, "td_rush": 0, "td_rec": 0,
                                               "car": 0, "tgt": 0})
        self.def_games = defaultdict(lambda: {"x_rush": 0.0, "x_rec": 0.0,
                                              "x_rec_pos": defaultdict(float)})
        self.player_games = defaultdict(lambda: {"x_rush": 0.0, "x_rec": 0.0, "car": 0, "tgt": 0,
                                                 "rz_car": 0, "rz_tgt": 0, "i10_car": 0, "i10_tgt": 0,
                                                 "td": 0, "team": None, "opp": None})
        self.names = {}
        for s_, plays in plays_by_season.items():
            for p in plays:
                x = self.rate.get((p["kind"], bucket(p["yl"])), 0.0)
                tg = self.team_games[(p["gid"], p["off"])]
                dg = self.def_games[(p["gid"], p["def"])]
                pg = self.player_games[(p["gid"], p["pid"])]
                pg["team"], pg["opp"] = p["off"], p["def"]
                self.names[p["pid"]] = p["name"]
                if p["kind"] == "rush":
                    tg["x_rush"] += x; tg["td_rush"] += p["td"]; tg["car"] += 1
                    dg["x_rush"] += x
                    pg["x_rush"] += x; pg["car"] += 1
                    pg["rz_car"] += p["yl"] <= 20; pg["i10_car"] += p["yl"] <= 10
                else:
                    tg["x_rec"] += x; tg["td_rec"] += p["td"]; tg["tgt"] += 1
                    dg["x_rec"] += x
                    dg["x_rec_pos"][self.pos.get(p["pid"], "WR")] += x
                    pg["x_rec"] += x; pg["tgt"] += 1
                    pg["rz_tgt"] += p["yl"] <= 20; pg["i10_tgt"] += p["yl"] <= 10
                pg["td"] += p["td"]

        self.by_pid = defaultdict(list)
        for (gid, pid), pg in self.player_games.items():
            self.by_pid[pid].append((gid, pg))
        self.team_gids = defaultdict(list)
        for (gid, t) in self.team_games:
            self.team_gids[t].append(gid)

        # League constants from last season (fallback: whatever we have).
        ref_games = [g for g in games if g["season"] == season - 1 and g["hs"] is not None] or \
                    [g for g in games if g["hs"] is not None]
        tot_td = tot_pts = 0.0
        for g in ref_games:
            for team, side in ((g["home"], "home"), (g["away"], "away")):
                tg = self.team_games.get((g["id"], team))
                imp = implied_points(g, side)
                if tg and imp:
                    tot_td += tg["td_rush"] + tg["td_rec"]
                    tot_pts += imp
        self.td_per_point = tot_td / tot_pts if tot_pts else 0.105
        xr = sum(t["x_rush"] for t in self.team_games.values())
        xp = sum(t["x_rec"] for t in self.team_games.values())
        self.league_rush_share = xr / (xr + xp) if xr + xp else 0.42
        pos_tot = defaultdict(float)
        for d in self.def_games.values():
            for k, v in d["x_rec_pos"].items():
                pos_tot[k] += v
        s = sum(pos_tot.values()) or 1
        self.league_rec_pos = {k: pos_tot[k] / s for k in ("RB", "WR", "TE")}
        self.league_ppg = (sum(g["hs"] + g["as"] for g in ref_games) / (2 * len(ref_games))) if ref_games else 22.0

    # ---- helpers -------------------------------------------------------
    def _weight(self, gid, team=None):
        back = self.season - self.games[gid]["season"]
        if back == 0:
            return 1.0
        w = HISTORY_WEIGHTS.get(back, 0.0)
        if team and COACH_W != 1.0:
            now, then = self.coaches.get((self.season, team)), self.coaches.get((self.games[gid]["season"], team))
            if now and then and now != then:
                w *= COACH_W
        return w

    def _before(self, gid, day):
        g = self.games.get(gid)
        return g is not None and g["day"] < day and \
            (g["season"] == self.season or (self.season - g["season"]) in HISTORY_WEIGHTS)

    def predict_game(self, game):
        """Return [{pid, name, team, opp, pos, lam, prob, ...}] for both teams in `game`."""
        day = game["day"]
        out = []
        for team, opp, side in ((game["home"], game["away"], "home"), (game["away"], game["home"], "away")):
            out.extend(self._predict_team(game, team, opp, side, day))
        return out

    def _team_hist(self, team, day, table):
        return [(self._weight(gid, team), table[(gid, team)]) for gid in self.team_gids[team]
                if (gid, team) in table and self._before(gid, day)]

    def _predict_team(self, game, team, opp, side, day):
        # 1. Expected offensive TDs for the team
        imp = implied_points(game, side) if USE_VEGAS else None
        if not imp:
            off_rows = [self._points(g, team) for g in self._played(team, day)]
            def_rows = [self._points(g, opp, allowed=True) for g in self._played(opp, day)]
            imp = 0.5 * (shrunk_mean(off_rows, self.league_ppg, 4) + shrunk_mean(def_rows, self.league_ppg, 4))
        lam_team = self.td_per_point * imp

        # 2. Rush/pass mix: team tendency x opponent allowed, log5 around league rate
        off = self._team_hist(team, day, self.team_games)
        dfn = self._team_hist(opp, day, self.def_games)
        r0 = self.league_rush_share
        r_off = shrunk_ratio(off, "x_rush", "x_rec", r0, 4)
        r_def = shrunk_ratio(dfn, "x_rush", "x_rec", r0, MATCHUP_K_MIX) if USE_MATCHUP else r0
        mix = log5(r_off, r_def, r0)
        lam_rush, lam_rec = lam_team * mix, lam_team * (1 - mix)

        # 4. Opponent's receiving-TD split by position (tilt), shrunk to league
        w_tot = sum(w for w, _ in dfn)
        pos_mult = {}
        for pos in ("RB", "WR", "TE"):
            num = sum(w * d["x_rec_pos"].get(pos, 0.0) for w, d in dfn)
            den = sum(w * d["x_rec"] for w, d in dfn)
            league = self.league_rec_pos.get(pos, 0.33)
            k = MATCHUP_K_POS
            share = (num + k * league * (den / max(w_tot, 1e-9) if w_tot else 1)) / (den + k * (den / max(w_tot, 1e-9) if w_tot else 1)) if den else league
            pos_mult[pos] = share / league if league else 1.0
        pos_mult["QB"] = 1.0
        if not USE_MATCHUP:
            pos_mult = {k: 1.0 for k in pos_mult}

        # 3. Player shares of the team's expected TDs
        team_game_ids = {gid for gid in self.team_gids[team] if self._before(gid, day)}
        latest = {}
        for (gid, pid), pg in self.player_games.items():
            if not self._before(gid, day):
                continue
            g = self.games[gid]
            if pid not in latest or g["day"] > latest[pid][0]:
                latest[pid] = (g["day"], pg["team"])
        ruled_out = game.get("out", set())
        # Ruled-out QBs stay in for now so a fill-in starter can inherit the QB role's usage.
        candidates = [pid for pid, (_, t) in latest.items() if t == team and pid in self.pos
                      and (pid not in ruled_out or self.pos[pid] == "QB")]

        team_days = sorted({self.games[g]["day"] for g in team_game_ids})
        last_team_game = team_days[-1] if team_days else None
        recent_days = set(team_days[-RECENT_GAMES:])
        rows = []
        for pid in candidates:
            sh = defaultdict(float)
            wsum = 0.0
            games_cur = 0
            stats = defaultdict(float)
            last_day = None
            recent = set()
            snap_hist = []
            for gid, pg in self.by_pid[pid]:
                if not self._before(gid, day):
                    continue
                w = self._weight(gid, team)
                if pg["team"] != team:
                    if not OTHER_TEAM_WEIGHT or self.games[gid]["season"] == self.season and False:
                        continue
                    w *= OTHER_TEAM_WEIGHT
                gs = self.games[gid]["season"]
                if gs != self.season:
                    w *= 1.0  # weight stays; aging scales the share itself below
                af = age_factor(self.pos[pid], self.births.get(pid), gs, self.season) if gs != self.season else 1.0
                tg = self.team_games[(gid, pg["team"])]
                wsum += w
                sh["x_rush"] += w * af * (pg["x_rush"] / tg["x_rush"] if tg["x_rush"] else 0)
                sh["x_rec"] += w * af * (pg["x_rec"] / tg["x_rec"] if tg["x_rec"] else 0)
                sh["car"] += w * af * (pg["car"] / tg["car"] if tg["car"] else 0)
                sh["tgt"] += w * af * (pg["tgt"] / tg["tgt"] if tg["tgt"] else 0)
                if self.games[gid]["season"] == self.season:
                    games_cur += 1
                    for k in ("rz_car", "rz_tgt", "i10_car", "i10_tgt", "td", "x_rush", "x_rec"):
                        stats[k] += pg[k]
                d = self.games[gid]["day"]
                if pg["team"] == team and (gid, pid) in self.snaps:
                    snap_hist.append((d, w, self.snaps[(gid, pid)]))
                recent.add(d)
                last_day = d if last_day is None or d > last_day else last_day
            if wsum == 0 or not (recent & recent_days):
                continue  # hasn't played in the team's last few games: likely injured, cut or inactive
            n = wsum
            rz_w = n / (n + 3.0)  # trust red-zone share more as games accumulate
            rush_share = rz_w * sh["x_rush"] / n + (1 - rz_w) * sh["car"] / n
            rec_share = rz_w * sh["x_rec"] / n + (1 - rz_w) * sh["tgt"] / n
            if SNAP_ALPHA and snap_hist:
                snap_hist.sort()
                hist_avg = sum(w * x for _, w, x in snap_hist) / sum(w for _, w, _ in snap_hist)
                rec3 = [x for _, _, x in snap_hist[-3:]]
                wts = [0.2, 0.3, 0.5][-len(rec3):]
                recent_snap = sum(a * b for a, b in zip(wts, rec3)) / sum(wts)
                if hist_avg > 0.05:
                    role = min(1.6, max(0.6, 1 + SNAP_ALPHA * (recent_snap / hist_avg - 1)))
                    rush_share *= role; rec_share *= role
            rows.append({"pid": pid, "pos": self.pos[pid], "rush_share": rush_share, "rec_share": rec_share,
                         "games": games_cur, "stats": stats,
                         "missed_last": last_team_game is not None and last_day != last_team_game})

        # Use the listed starting QB: drop other QBs and give the listed starter the QB role's share.
        qb_id, qb_name = (game.get("hqb_id"), game.get("hqb")) if side == "home" else (game.get("aqb_id"), game.get("aqb"))
        if qb_id and qb_id not in ruled_out:
            others = [r for r in rows if r["pos"] == "QB" and r["pid"] != qb_id]
            if others and not any(r["pid"] == qb_id for r in rows):
                role = max(others, key=lambda r: r["games"] + r["rush_share"])
                rows.append({**role, "pid": qb_id, "games": 0, "stats": defaultdict(float), "missed_last": False,
                             "fill_in": True})
                self.names.setdefault(qb_id, qb_name or qb_id)
            rows = [r for r in rows if not (r["pos"] == "QB" and r["pid"] != qb_id)]
        rows = [r for r in rows if r["pid"] not in ruled_out]

        # Hand the team's full share of expected TDs to the players still around.
        for key in ("rush_share", "rec_share"):
            tot = sum(r[key] for r in rows)
            if tot > 0:
                for r in rows:
                    r[key] /= tot
        tilt_den = sum(r["rec_share"] * pos_mult.get(r["pos"], 1) for r in rows)
        tilt_num = sum(r["rec_share"] for r in rows)
        tilt_norm = tilt_num / tilt_den if tilt_den else 1.0

        out = []
        for r in rows:
            lam_r = lam_rush * r["rush_share"]
            lam_c = lam_rec * r["rec_share"] * pos_mult.get(r["pos"], 1) * tilt_norm
            lam = (lam_r + lam_c) * CALIBRATION
            out.append({
                "pid": r["pid"], "name": self.names.get(r["pid"], r["pid"]), "team": team, "opp": opp,
                "pos": r["pos"], "lam": lam, "prob": 1 - math.exp(-lam),
                "lam_rush": lam_r, "lam_rec": lam_c,
                "rush_share": r["rush_share"], "rec_share": r["rec_share"],
                "pos_mult": pos_mult.get(r["pos"], 1.0),
                "team_tds": lam_team, "rush_mix": mix, "implied": imp,
                "games": r["games"], "missed_last": r["missed_last"],
                "rz_car": int(r["stats"]["rz_car"]), "rz_tgt": int(r["stats"]["rz_tgt"]),
                "i10_car": int(r["stats"]["i10_car"]), "i10_tgt": int(r["stats"]["i10_tgt"]),
                "td": int(r["stats"]["td"]), "xtd": r["stats"]["x_rush"] + r["stats"]["x_rec"],
                "fill_in": r.get("fill_in", False),
            })
        return out

    def _played(self, team, day):
        return [g for g in self.games.values() if g["hs"] is not None and g["day"] < day
                and self._weight(g["id"]) > 0 and team in (g["home"], g["away"])]

    def _points(self, g, team, allowed=False):
        mine = g["hs"] if g["home"] == team else g["as"]
        theirs = g["as"] if g["home"] == team else g["hs"]
        return (self._weight(g["id"]), theirs if allowed else mine)


def implied_points(g, side):
    """Vegas implied points. nflverse spread_line > 0 means the home team is favored."""
    if g.get("total") is None or g.get("spread") is None:
        return None
    s = g["spread"] if side == "home" else -g["spread"]
    return g["total"] / 2 + s / 2


def shrunk_ratio(rows, a, b, prior, k):
    num = sum(w * v[a] for w, v in rows)
    den = sum(w * (v[a] + v[b]) for w, v in rows)
    n = sum(w for w, _ in rows)
    if den <= 0:
        return prior
    per_game = den / n
    return (num + k * per_game * prior) / (den + k * per_game)


def shrunk_mean(rows, prior, k):
    n = sum(w for w, _ in rows)
    return (sum(w * v for w, v in rows) + k * prior) / (n + k)


def log5(a, b, base):
    odds = lambda p: p / (1 - p)
    o = odds(min(max(a, 0.01), 0.99)) * odds(min(max(b, 0.01), 0.99)) / odds(min(max(base, 0.01), 0.99))
    return o / (1 + o)


# ---------------------------------------------------------------------------
# Yardage and volume props model (receiving/rushing yards, receptions, rush attempts)
# Backtest on 2025 (distribution fit on 2024): mean error about 4% lower than the player's own season
# average for receiving yards and receptions, 3% for rush attempts and 1.6% for rushing yards.
# Snap counts, pace (Vegas total + opponent plays), weather, the starting QB's efficiency and missing
# defensive backs each helped in both 2024 and 2025. Head-coach changes and play-calling tendencies
# (neutral pass rate over expected) were tested too; they added nothing beyond team history, so they're off.
# ---------------------------------------------------------------------------
REC_POS = ("RB", "WR", "TE")
RUSH_POS = ("QB", "RB")
STATS = ("rec_yds", "rec", "rush_yds", "rush_att")

K = {
    "team_games": 3.0,      # games of league average mixed into a team's volume
    "opp_games": 8.0,       # games of league average mixed into a defense's volume allowed
    "ypt": 60.0,            # targets of position-average yards per target
    "catch": 40.0,          # targets of position-average catch rate
    "ypc": 120.0,           # carries of position-average yards per carry
    "opp_ypt": 80.0,        # targets of league average in a defense's yards per target allowed
    "opp_catch": 80.0,
    "opp_ypc": 150.0,
}
RECENT_BOOST = 2.0          # extra weight on a player's last three games with the team
PROPS_MATCHUP = True
PROPS_SNAP_ALPHA = 0.5            # how far a player's recent snap share moves his projected role (0 = ignore snaps)
USE_PACE = True             # Vegas total and opponent pace adjust team volume
PACE_BETA = 0.5             # how much of the opponent's pace carries over
USE_WEATHER = True          # wind and cold adjust passing/rushing volume and efficiency
LEAGUE_TOTAL = 45.0
QB_ALPHA = 0.5              # how strongly the starting QB's own efficiency moves his receivers' yards and catch rate
K_QB = 150.0                # pass attempts of backup-level passing mixed into each QB's efficiency
DEF_INJ_PASS = 0.05         # extra yards per target allowed per full-time defensive back (or half of an edge rusher) out
DEF_INJ_RUN = 0.0           # extra yards per carry allowed per full-time front-seven player out
PROPS_COACH_W = 1.0               # weight on past seasons for a new head coach (tested 0.25-0.75: no clear gain, so off)
# Questionable players keep this share of their usual targets/carries, by how much they practiced that week.
# Backtests: small but consistent gains on 2024 and 2025 for every yardage and volume stat.
PRACTICE_FACTOR = {"dnp": 0.85, "limited": 0.90, "full": 0.95}
# Rookies: their target share starts from the typical rookie share for their position and draft round, worth
# one game of their own data. Backtests: better receiving yards and receptions in 2024 and 2025. Applying it to
# carries made rushing worse, so it's receiving only. (Air-yards share and per-player outcome ranges by
# target depth were also tested and made things worse, so they're not used.)
DRAFT_K = 1.0
TENDENCY_B = 0.0            # (tested: already captured by team history, so off) how much play-calling tendencies (neutral-situation pass rate over expected) shift targets vs carries
DB_POS = {"CB", "S", "DB", "FS", "SS"}
EDGE_POS = {"DE", "OLB", "EDGE"}
FRONT_POS = {"DT", "NT", "DL", "DE", "LB", "ILB", "MLB", "OLB", "EDGE"}


class PropsModel:
    def __init__(self, rows, games, season, history_weights, age_factor, positions, snaps=None, weather=None,
                 coaches=None, tendencies=None, def_snaps=None, def_out=None, draft=None):
        """
        rows: player-game dicts {season, gid, team, opp, pid, name, pos, tgt, rec, rec_yds, car, rush_yds}
        games: {gid: {id, season, day, home, away, spread, total, ...}}
        history_weights: {1: w, 2: w, ...}; age_factor(pos, pid, from_season, to_season) -> float
        """
        self.season, self.hw, self.age_factor = season, history_weights, age_factor
        self.games = games
        self.names, self.pos = {}, positions
        self.snaps = snaps or {}          # (gid, pid) -> offensive snap share 0-1
        self.weather = weather or {}      # gid -> {"wind": mph, "temp": F, "covered": bool}
        self.coaches = coaches or {}      # (season, team) -> head coach
        self.tend = tendencies or {}      # (gid, team, "off"|"def") -> [neutral plays, passes, expected passes]
        self.def_snaps = def_snaps or {}  # pid -> [(day, defensive snap share)]
        self.def_out = def_out or {}      # gid -> {team: [(pid, position)]} defenders ruled out
        self.draft = draft or {}          # pid -> (draft round or None if undrafted, rookie season)
        self.qb_games = defaultdict(list) # (gid, team) -> [(pid, attempts)]
        self.team = defaultdict(lambda: defaultdict(float))      # (gid, team) -> totals
        self.dfn = defaultdict(lambda: defaultdict(float))       # (gid, opp) -> totals allowed (by pos)
        self.player = defaultdict(list)                          # pid -> [row]
        for r in rows:
            if r["gid"] not in games:
                continue
            t = self.team[(r["gid"], r["team"])]
            d = self.dfn[(r["gid"], r["opp"])]
            for k in ("tgt", "rec", "rec_yds", "car", "rush_yds"):
                t[k] += r[k]
                d[k] += r[k]
                d[f"{r['pos']}_{k}"] += r[k]
            self.player[r["pid"]].append(r)
            self.names[r["pid"]] = r["name"]
            if r.get("att"):
                self.qb_games[(r["gid"], r["team"])].append((r["pid"], r["att"]))
        for rs in self.player.values():
            rs.sort(key=lambda r: games[r["gid"]]["day"])
        self.team_gids = defaultdict(list)
        for (gid, t) in self.team:
            self.team_gids[t].append(gid)
        self._fit_league()
        self._fit_rookies()

    def _fit_rookies(self):
        """Average rookie-season target share by position and draft round (earlier seasons only)."""
        acc = defaultdict(lambda: [0.0, 0])
        for pid, rs in self.player.items():
            d = self.draft.get(pid)
            if not d:
                continue
            for r in rs:
                if self.games[r["gid"]]["season"] == d[1] < self.season:
                    tv = self.team[(r["gid"], r["team"])]
                    a_ = acc[(self.pos.get(pid), _round_bucket(d[0]))]
                    a_[0] += r["tgt"] / tv["tgt"] if tv["tgt"] else 0
                    a_[1] += 1
        self.draft_prior = {k: v[0] / v[1] for k, v in acc.items() if v[1] >= 20}

    # ---------------------------------------------------------------- setup
    def _w(self, gid, team=None):
        back = self.season - self.games[gid]["season"]
        if back == 0:
            return 1.0
        w = self.hw.get(back, 0.0)
        if team and PROPS_COACH_W != 1.0:
            now, then = self.coaches.get((self.season, team)), self.coaches.get((self.games[gid]["season"], team))
            if now and then and now != then:
                w *= PROPS_COACH_W
        return w

    def _fit_league(self):
        prior = [(gid, t, v) for (gid, t), v in self.team.items() if self.games[gid]["season"] < self.season]
        base = prior or [(gid, t, v) for (gid, t), v in self.team.items()]
        n = max(len(base), 1)
        self.lg = {k: sum(v[k] for _, _, v in base) / n for k in ("tgt", "rec", "rec_yds", "car", "rush_yds")}
        # league efficiency by position (from prior seasons)
        pos_tot = defaultdict(float)
        for (gid, o), d in self.dfn.items():
            if self.games[gid]["season"] < self.season or not prior:
                for k, v in d.items():
                    pos_tot[k] += v
        self.lg_pos = {}
        for p in ("QB", "RB", "WR", "TE"):
            tg, rc, ry = pos_tot[f"{p}_tgt"], pos_tot[f"{p}_rec"], pos_tot[f"{p}_rec_yds"]
            ca, ru = pos_tot[f"{p}_car"], pos_tot[f"{p}_rush_yds"]
            self.lg_pos[p] = {"ypt": ry / tg if tg else 7.0, "catch": rc / tg if tg else 0.65,
                              "ypc": ru / ca if ca else 4.2}
        self.lg_pos_share = {p: (pos_tot[f"{p}_tgt"] / pos_tot["tgt"] if pos_tot["tgt"] else 0.3) for p in REC_POS}
        self.lg_ypc = pos_tot["rush_yds"] / pos_tot["car"] if pos_tot["car"] else 4.3
        # game-script sensitivity: change in team carries/targets per point of spread (team perspective)
        seas = defaultdict(lambda: [0.0, 0.0, 0])
        for gid, t, v in base:
            s = seas[(self.games[gid]["season"], t)]
            s[0] += v["car"]; s[1] += v["tgt"]; s[2] += 1
        xs, yc, yt = [], [], []
        for gid, t, v in base:
            g = self.games[gid]
            if g.get("spread") is None:
                continue
            sp = g["spread"] if g["home"] == t else -g["spread"]
            s = seas[(g["season"], t)]
            if s[0] and s[1]:
                xs.append(sp); yc.append(v["car"] / (s[0] / s[2]) - 1); yt.append(v["tgt"] / (s[1] / s[2]) - 1)
        den = sum(x * x for x in xs) or 1
        self.b_car = sum(x * y for x, y in zip(xs, yc)) / den
        self.b_tgt = sum(x * y for x, y in zip(xs, yt)) / den
        # Vegas total: change in team carries/targets per point of total above/below league average
        tots = [g["total"] for g in self.games.values() if g.get("total") is not None]
        self.lg_total = sum(tots) / len(tots) if tots else LEAGUE_TOTAL
        xs, yc, yt = [], [], []
        for gid, t, v in base:
            g = self.games[gid]
            if g.get("total") is None:
                continue
            s = seas[(g["season"], t)]
            if s[0] and s[1]:
                xs.append(g["total"] - self.lg_total); yc.append(v["car"] / (s[0] / s[2]) - 1); yt.append(v["tgt"] / (s[1] / s[2]) - 1)
        den = sum(x * x for x in xs) or 1
        self.b_tot_car = sum(x * y for x, y in zip(xs, yc)) / den
        self.b_tot_tgt = sum(x * y for x, y in zip(xs, yt)) / den
        # Weather: team volume and efficiency vs wind above 10 mph and cold below 40F (outdoor games)
        eff = defaultdict(lambda: [0.0, 0.0, 0.0, 0.0])
        for gid, t, v in base:
            e = eff[(self.games[gid]["season"], t)]
            e[0] += v["rec_yds"]; e[1] += v["tgt"]; e[2] += v["rush_yds"]; e[3] += v["car"]
        feats = {k: [] for k in ("tgt", "car", "ypt", "ypc")}
        X = []
        for gid, t, v in base:
            w = self.weather.get(gid)
            if not w or w.get("covered") or w.get("wind") is None:
                continue
            s = seas[(self.games[gid]["season"], t)]; e = eff[(self.games[gid]["season"], t)]
            if not (s[0] and s[1] and v["tgt"] and v["car"] and e[1] and e[3]):
                continue
            X.append((max(0.0, w["wind"] - 10), max(0.0, 40 - (w["temp"] if w.get("temp") is not None else 60))))
            feats["tgt"].append(v["tgt"] / (s[1] / s[2]) - 1)
            feats["car"].append(v["car"] / (s[0] / s[2]) - 1)
            feats["ypt"].append((v["rec_yds"] / v["tgt"]) / (e[0] / e[1]) - 1)
            feats["ypc"].append((v["rush_yds"] / v["car"]) / (e[2] / e[3]) - 1)
        self.wx = {}
        for k, ys in feats.items():
            self.wx[k] = _ols2(X, ys)
        # passing efficiency prior for QBs with little history: backup-level QBs (under 150 attempts in a season)
        qs = defaultdict(lambda: [0.0, 0.0, 0.0])
        for pid, prs in self.player.items():
            for r in prs:
                if r.get("att") and self.games[r["gid"]]["season"] < self.season:
                    q = qs[(pid, self.games[r["gid"]]["season"])]
                    q[0] += r["att"]; q[1] += r.get("cmp", 0); q[2] += r.get("pyd", 0)
        small = [v for v in qs.values() if v[0] < 150]
        a = sum(v[0] for v in small)
        self.qb_prior = {"ypa": sum(v[2] for v in small) / a if a else 6.2, "cmp": sum(v[1] for v in small) / a if a else 0.62}

    def _before(self, gid, day):
        g = self.games[gid]
        return g["day"] < day and self._w(gid) > 0

    # ---------------------------------------------------------------- predict
    def predict_game(self, game, ruled_out=frozenset()):
        out = []
        for team, opp, side in ((game["home"], game["away"], "home"), (game["away"], game["home"], "away")):
            out.extend(self._predict_team(game, team, opp, side, ruled_out))
        return out

    def _qb_eff(self, pid, day):
        a = c = y = 0.0
        for r in self.player.get(pid, []):
            if r.get("att") and self._before(r["gid"], day):
                w = self._w(r["gid"])
                a += w * r["att"]; c += w * r.get("cmp", 0); y += w * r.get("pyd", 0)
        return ((y + K_QB * self.qb_prior["ypa"]) / (a + K_QB), (c + K_QB * self.qb_prior["cmp"]) / (a + K_QB))

    def _qb_factor(self, game, team, side, day):
        """Starting QB's efficiency vs the QBs behind the team's history (yards per attempt, completion rate)."""
        if not QB_ALPHA:
            return 1.0, 1.0
        starter = game.get("hqb_id") if side == "home" else game.get("aqb_id")
        if not starter:
            return 1.0, 1.0
        ws = wy = wc = 0.0
        cache = {}
        for g in self.team_gids[team]:
            if not self._before(g, day) or not self.qb_games.get((g, team)):
                continue
            main = max(self.qb_games[(g, team)], key=lambda x: x[1])[0]
            if main not in cache:
                cache[main] = self._qb_eff(main, day)
            w = self._w(g, team)
            ws += w; wy += w * cache[main][0]; wc += w * cache[main][1]
        if not ws:
            return 1.0, 1.0
        sy, sc = self._qb_eff(starter, day)
        return (sy / (wy / ws)) ** QB_ALPHA, (sc / (wc / ws)) ** QB_ALPHA

    def _def_injury(self, game, opp, day):
        """Yards-per-target and yards-per-carry multipliers for a defense missing regulars."""
        if not (DEF_INJ_PASS or DEF_INJ_RUN):
            return 1.0, 1.0
        p = r_ = 0.0
        for pid, pos in self.def_out.get(game["id"], {}).get(opp, []):
            hist = [x for d, x in self.def_snaps.get(pid, []) if d < day][-4:]
            if not hist:
                continue
            share = sum(hist) / len(hist)
            if pos in DB_POS:
                p += share
            if pos in EDGE_POS:
                p += 0.5 * share
            if pos in FRONT_POS:
                r_ += share
        # relative to a typical week (every team is usually missing someone)
        base_p, base_r = self._typical_def_missing()
        return 1 + DEF_INJ_PASS * (p - base_p), 1 + DEF_INJ_RUN * (r_ - base_r)

    def _typical_def_missing(self):
        if hasattr(self, "_tdm"):
            return self._tdm
        tp = tr = n = 0.0
        for gid, teams in self.def_out.items():
            g = self.games.get(gid)
            if not g:
                continue
            for team, lst in teams.items():
                n += 1
                for pid, pos in lst:
                    hist = [x for d, x in self.def_snaps.get(pid, []) if d < g["day"]][-4:]
                    if not hist:
                        continue
                    sh = sum(hist) / len(hist)
                    tp += sh if pos in DB_POS else 0
                    tp += 0.5 * sh if pos in EDGE_POS else 0
                    tr += sh if pos in FRONT_POS else 0
        self._tdm = (tp / n, tr / n) if n else (0.0, 0.0)
        return self._tdm

    def _tendency(self, team, opp, day):
        """Neutral-situation pass rate over expected: the offense's play-calling plus what this defense invites."""
        def rate(t, kind, k_plays=140.0):
            n = pw = 0.0
            for g in self.team_gids[t]:
                v = self.tend.get((g, t, kind))
                if v and self._before(g, day):
                    w = self._w(g, t)
                    n += w * v[0]; pw += w * (v[1] - v[2])
            return pw / (n + k_plays)  # shrunk toward 0 (league-typical) by about four games of neutral plays
        return rate(team, "off") + rate(opp, "def")

    def _wx_factor(self, gid, key):
        if not USE_WEATHER:
            return 1.0
        w = self.weather.get(gid)
        if not w or w.get("covered") or w.get("wind") is None:
            return 1.0
        bw, bc = self.wx.get(key, (0.0, 0.0))
        f = 1 + bw * max(0.0, w["wind"] - 10) + bc * max(0.0, 40 - (w["temp"] if w.get("temp") is not None else 60))
        return min(1.3, max(0.7, f))

    def _team_volume(self, team, opp, day, spread, game=None):
        def shrunk(rows, key, prior, k):
            n = sum(w for w, _ in rows)
            return (sum(w * v[key] for w, v in rows) + k * prior) / (n + k)
        trows = [(self._w(g, team), self.team[(g, team)]) for g in self.team_gids[team] if self._before(g, day)]
        drows = [(self._w(g, opp), self.dfn[(g, opp)]) for g in self.team_gids[opp]
                 if (g, opp) in self.dfn and self._before(g, day)]
        vol = {}
        pace_f = 1.0
        if USE_PACE:
            # opponent's own offensive plays (carries + targets) per game vs league: faster opponents add possessions
            orows = [(self._w(g), self.team[(g, opp)]) for g in self.team_gids[opp] if self._before(g, day)]
            lg_plays = self.lg["car"] + self.lg["tgt"]
            n = sum(w for w, _ in orows)
            opp_plays = (sum(w * (v["car"] + v["tgt"]) for w, v in orows) + K["opp_games"] * lg_plays) / (n + K["opp_games"])
            pace_f = (opp_plays / lg_plays) ** PACE_BETA
        tot = game.get("total") if game else None
        for key, b, bt in (("car", self.b_car, self.b_tot_car), ("tgt", self.b_tgt, self.b_tot_tgt)):
            base = shrunk(trows, key, self.lg[key], K["team_games"])
            opp_f = shrunk(drows, key, self.lg[key], K["opp_games"]) / self.lg[key] if PROPS_MATCHUP else 1.0
            script = 1 + b * (spread or 0)
            tot_f = 1 + bt * (tot - self.lg_total) if USE_PACE and tot is not None else 1.0
            tend = self._tendency(team, opp, day) if TENDENCY_B else 0.0
            tend_f = 1 + TENDENCY_B * tend * (1 if key == "tgt" else -1)
            vol[key] = base * script * opp_f * pace_f * tot_f * tend_f * (self._wx_factor(game["id"], key) if game else 1.0)
        return vol, drows

    def _opp_eff(self, drows, pos):
        if not PROPS_MATCHUP:
            return {"ypt": 1.0, "catch": 1.0, "ypc": 1.0}
        lp = self.lg_pos[pos]
        tg = sum(w * d[f"{pos}_tgt"] for w, d in drows)
        ry = sum(w * d[f"{pos}_rec_yds"] for w, d in drows)
        rc = sum(w * d[f"{pos}_rec"] for w, d in drows)
        ca = sum(w * d["car"] for w, d in drows)
        ru = sum(w * d["rush_yds"] for w, d in drows)
        return {
            "ypt": ((ry + K["opp_ypt"] * lp["ypt"]) / (tg + K["opp_ypt"])) / lp["ypt"],
            "catch": ((rc + K["opp_catch"] * lp["catch"]) / (tg + K["opp_catch"])) / lp["catch"],
            "ypc": ((ru + K["opp_ypc"] * self.lg_ypc) / (ca + K["opp_ypc"])) / self.lg_ypc,
        }

    def _predict_team(self, game, team, opp, side, ruled_out):
        day = game["day"]
        spread = game.get("spread")
        spread_t = None if spread is None else (spread if side == "home" else -spread)
        vol, drows = self._team_volume(team, opp, day, spread_t, game)
        team_days = sorted({self.games[g]["day"] for g in self.team_gids[team] if self._before(g, day)})
        recent_days = set(team_days[-3:])
        last2 = set(team_days[-2:])

        rows = []
        for pid, prs in self.player.items():
            pos = self.pos.get(pid)
            if pos not in ("QB", "RB", "WR", "TE") or pid in ruled_out:
                continue
            hist = [r for r in prs if self._before(r["gid"], day)]
            if not hist or hist[-1]["team"] != team:
                continue
            mine = [r for r in hist if r["team"] == team]
            if not (last2 & {self.games[r["gid"]]["day"] for r in mine}):
                continue
            sw = st = sc = 0.0
            eff = defaultdict(float)
            n_cur = 0
            for r in mine:
                g = self.games[r["gid"]]
                w = self._w(r["gid"], team)
                if g["day"] in recent_days:
                    w *= 1 + RECENT_BOOST
                af = 1.0 if g["season"] == self.season else self.age_factor(pos, pid, g["season"], self.season)
                tv = self.team[(r["gid"], team)]
                sw += w
                st += w * af * (r["tgt"] / tv["tgt"] if tv["tgt"] else 0)
                sc += w * af * (r["car"] / tv["car"] if tv["car"] else 0)
                for k in ("tgt", "rec", "rec_yds", "car", "rush_yds"):
                    eff[k] += w * r[k]
                n_cur += g["season"] == self.season
            tshare, cshare = st / sw, sc / sw
            d = self.draft.get(pid)
            if DRAFT_K and d and d[1] == self.season and pos in REC_POS:
                prior = self.draft_prior.get((pos, _round_bucket(d[0])))
                if prior is not None:
                    tshare = (n_cur * tshare + DRAFT_K * prior) / (n_cur + DRAFT_K)
            role = 1.0
            if PROPS_SNAP_ALPHA and self.snaps:
                # recent snap share (last 3 team games he played, newest weighted most) vs his average in the games used
                sn = [(self._w(r["gid"]) * (1 + RECENT_BOOST if self.games[r["gid"]]["day"] in recent_days else 1),
                       self.snaps.get((r["gid"], pid))) for r in mine]
                sn = [(w, x) for w, x in sn if x is not None]
                rec = [self.snaps.get((r["gid"], pid)) for r in mine[-3:]]
                rec = [x for x in rec if x is not None]
                if sn and rec:
                    hist_avg = sum(w * x for w, x in sn) / sum(w for w, _ in sn)
                    wts = [0.2, 0.3, 0.5][-len(rec):]
                    recent = sum(w * x for w, x in zip(wts, rec)) / sum(wts)
                    if hist_avg > 0.05:
                        role = min(1.6, max(0.6, 1 + PROPS_SNAP_ALPHA * (recent / hist_avg - 1)))
            tshare *= role; cshare *= role
            q = game.get("questionable", {}).get(pid)
            if q:
                tshare *= PRACTICE_FACTOR.get(q, 1.0); cshare *= PRACTICE_FACTOR.get(q, 1.0)
            rows.append({"pid": pid, "pos": pos, "tshare": tshare, "cshare": cshare, "eff": eff, "n": n_cur,
                         "hist": [r for r in mine if self.games[r["gid"]]["season"] == self.season]})
        # hand departed/ruled-out players' volume to those still here
        for key in ("tshare", "cshare"):
            tot = sum(r[key] for r in rows)
            if tot > 0:
                for r in rows:
                    r[key] /= tot

        qb_ypt, qb_cmp = self._qb_factor(game, team, side, day)
        di_pass, di_run = self._def_injury(game, opp, day)
        out = []
        for r in rows:
            pos, e, lp = r["pos"], r["eff"], self.lg_pos[r["pos"]]
            oe = self._opp_eff(drows, pos)
            tgt = vol["tgt"] * r["tshare"]
            car = vol["car"] * r["cshare"]
            ypt = (e["rec_yds"] + K["ypt"] * lp["ypt"]) / (e["tgt"] + K["ypt"])
            catch = (e["rec"] + K["catch"] * lp["catch"]) / (e["tgt"] + K["catch"])
            ypc = (e["rush_yds"] + K["ypc"] * lp["ypc"]) / (e["car"] + K["ypc"])
            wx_ypt, wx_ypc = self._wx_factor(game["id"], "ypt"), self._wx_factor(game["id"], "ypc")
            ypt *= wx_ypt * qb_ypt * di_pass; ypc *= wx_ypc * di_run
            catch *= qb_cmp
            proj = {
                "rec_yds": tgt * ypt * oe["ypt"] if pos in REC_POS else None,
                "rec": tgt * min(0.95, catch * oe["catch"]) if pos in REC_POS else None,
                "rush_yds": car * ypc * oe["ypc"] if pos in RUSH_POS else None,
                "rush_att": car if pos in RUSH_POS else None,
            }
            h = r["hist"]
            avg = lambda k: (sum(x[k] for x in h) / len(h)) if h else None
            l3 = lambda k: (sum(x[k] for x in h[-3:]) / len(h[-3:])) if h else None
            out.append({
                "pid": r["pid"], "name": self.names.get(r["pid"], r["pid"]), "team": team, "opp": opp, "pos": pos,
                "proj": proj, "tgt": tgt, "car": car, "tshare": r["tshare"], "cshare": r["cshare"],
                "opp_eff": oe, "n": r["n"],
                "avg": {"rec_yds": avg("rec_yds"), "rec": avg("rec"), "rush_yds": avg("rush_yds"), "rush_att": avg("car"),
                        "tgt": avg("tgt")},
                "l3": {"rec_yds": l3("rec_yds"), "rec": l3("rec"), "rush_yds": l3("rush_yds"), "rush_att": l3("car")},
                "log": [[x["rec_yds"], x["rec"], x["rush_yds"], x["car"]] for x in h[-6:]],
            })
        return out


def _ols2(X, ys):
    """Least squares through the origin for two features; returns (b_wind, b_cold)."""
    if len(X) < 30:
        return (0.0, 0.0)
    a11 = sum(x[0] * x[0] for x in X); a12 = sum(x[0] * x[1] for x in X); a22 = sum(x[1] * x[1] for x in X)
    b1 = sum(x[0] * y for x, y in zip(X, ys)); b2 = sum(x[1] * y for x, y in zip(X, ys))
    det = a11 * a22 - a12 * a12
    if abs(det) < 1e-9:
        return (b1 / a11 if a11 else 0.0, 0.0)
    return ((a22 * b1 - a12 * b2) / det, (a11 * b2 - a12 * b1) / det)


def _round_bucket(rnd):
    return "1" if rnd == 1 else "2" if rnd == 2 else "3" if rnd == 3 else "4-7" if rnd else "UDFA"


def mu_bucket(stat, mu):
    """Projection size bucket for the outcome distribution (small projections are relatively noisier)."""
    cuts = {"rec_yds": (20, 45), "rec": (2, 4), "rush_yds": (25, 55), "rush_att": (6, 13)}[stat]
    return 0 if mu < cuts[0] else 1 if mu < cuts[1] else 2


def quantiles(values, n=201):
    v = sorted(values)
    return [round(v[min(len(v) - 1, int(i * (len(v) - 1) / (n - 1)))], 4) for i in range(n)]


def p_over(mu, qs, line):
    """Share of the outcome distribution above the line, treating the quantiles as equally likely."""
    if mu is None:
        return None
    return sum(1 for q in qs if mu * q > line) / len(qs)


# Spread of actual / projected outcomes from 2024-2025 backtests, by stat and projection size (201 quantiles)
RATIO_Q = {"rush_yds|0":[-3.1447,-0.8894,-0.542,-0.3861,-0.3013,-0.2542,-0.2103,-0.1787,-0.1415,-0.112,-0.087,-0.0619,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0436,0.061,0.0858,0.1006,0.1206,0.1327,0.151,0.1666,0.1788,0.1887,0.2047,0.2128,0.2177,0.2274,0.2396,0.2523,0.2625,0.2791,0.2899,0.2998,0.3144,0.3241,0.3311,0.3434,0.3579,0.3728,0.3827,0.394,0.4213,0.4413,0.4589,0.4762,0.4856,0.4978,0.5057,0.5156,0.5359,0.5545,0.5708,0.5888,0.6062,0.6165,0.6323,0.6509,0.6659,0.6863,0.7023,0.7195,0.7395,0.76,0.7909,0.81,0.8313,0.8566,0.8736,0.8912,0.9061,0.9267,0.9475,0.9643,0.9844,1.0052,1.0295,1.0436,1.0568,1.0823,1.1113,1.1239,1.1394,1.1703,1.1909,1.2266,1.2466,1.2774,1.2985,1.3267,1.3671,1.3935,1.4146,1.4317,1.4592,1.4838,1.5238,1.5602,1.5959,1.6187,1.6495,1.6868,1.7127,1.7508,1.8058,1.8359,1.8648,1.893,1.942,1.9672,2.0224,2.0657,2.1355,2.1587,2.1908,2.2434,2.2936,2.3635,2.4095,2.4729,2.5184,2.5852,2.6397,2.6642,2.7599,2.8399,2.8861,2.9688,3.0207,3.0929,3.23,3.2989,3.3765,3.5186,3.5872,3.7093,3.8425,3.9479,4.0683,4.2522,4.4796,4.748,5.0079,5.6158,5.9012,6.5014,7.8039,8.7716,10.107,14.354,70.9323],"rush_att|0":[0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.1798,0.1902,0.2131,0.2295,0.2492,0.2634,0.2729,0.2856,0.3021,0.3147,0.3346,0.3426,0.3511,0.3611,0.3693,0.3802,0.3893,0.3979,0.4179,0.4306,0.445,0.4521,0.4637,0.4769,0.4895,0.4999,0.513,0.5212,0.5258,0.5387,0.5501,0.5575,0.569,0.581,0.5868,0.5949,0.6001,0.6143,0.6323,0.6493,0.6619,0.6715,0.6846,0.6897,0.6963,0.7019,0.713,0.7266,0.7363,0.7525,0.7651,0.782,0.796,0.8058,0.8167,0.8323,0.8461,0.8573,0.867,0.8737,0.8785,0.8892,0.8965,0.9087,0.9155,0.9292,0.9427,0.9632,0.9704,0.9797,0.9921,1.0052,1.0183,1.0289,1.0378,1.0501,1.057,1.066,1.0801,1.0879,1.0961,1.1165,1.1284,1.146,1.1741,1.1894,1.2021,1.2121,1.2258,1.2369,1.2514,1.2619,1.269,1.2896,1.3041,1.3152,1.3274,1.3415,1.3514,1.3645,1.3945,1.4088,1.4277,1.4559,1.4696,1.4938,1.5074,1.5174,1.5301,1.5566,1.5725,1.5896,1.6159,1.6469,1.6692,1.6885,1.7105,1.7224,1.7353,1.7537,1.7749,1.7924,1.8319,1.8454,1.8675,1.8853,1.9085,1.9327,1.9503,1.9728,2.0041,2.028,2.0509,2.0865,2.1039,2.163,2.2032,2.2324,2.2891,2.3556,2.4006,2.4778,2.5337,2.6026,2.6706,2.7149,2.7841,2.8482,2.9257,3.005,3.1138,3.2244,3.424,3.6221,3.7135,3.8823,3.9833,4.3195,4.6131,5.314,6.7875,8.4799,14.5051],"rec_yds|0":[-3.0929,-0.3691,-0.1595,-0.053,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0864,0.1123,0.146,0.1659,0.1914,0.2246,0.2471,0.2662,0.2814,0.2988,0.3224,0.3388,0.352,0.371,0.394,0.4117,0.4305,0.451,0.4672,0.4828,0.507,0.5258,0.551,0.5715,0.5938,0.6143,0.6325,0.6486,0.6654,0.6853,0.7093,0.7357,0.7549,0.7796,0.8026,0.8158,0.8308,0.8521,0.8639,0.879,0.898,0.9215,0.9396,0.9586,0.9871,1.0086,1.0261,1.0545,1.0729,1.1,1.1284,1.1445,1.169,1.1975,1.2335,1.2565,1.285,1.3173,1.3346,1.3704,1.3948,1.4296,1.4614,1.4876,1.5078,1.5339,1.5584,1.6061,1.6406,1.677,1.703,1.7426,1.7758,1.7922,1.8258,1.8535,1.8846,1.9283,1.968,1.9981,2.0439,2.0909,2.138,2.1846,2.2363,2.2812,2.3314,2.3872,2.4496,2.5219,2.578,2.6437,2.6961,2.7868,2.8549,2.9559,3.0277,3.1285,3.2429,3.389,3.5312,3.6385,3.772,3.9206,4.0779,4.1928,4.3839,4.6505,4.8942,5.156,5.391,5.8536,6.5517,7.4736,8.2858,10.4285,13.5305,43.6504],"rec|0":[0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.5024,0.511,0.515,0.5274,0.5354,0.5427,0.5504,0.5581,0.5697,0.5788,0.5852,0.5968,0.6064,0.6163,0.6241,0.6305,0.6381,0.6516,0.6639,0.6736,0.6842,0.6916,0.7021,0.7152,0.7232,0.731,0.7481,0.7615,0.7744,0.7906,0.805,0.8151,0.8309,0.845,0.8523,0.8663,0.8891,0.9033,0.9187,0.937,0.9565,0.9743,0.9871,1.0063,1.0157,1.0228,1.0363,1.0447,1.0571,1.0654,1.0716,1.0836,1.0981,1.1103,1.1251,1.1373,1.1526,1.1675,1.1779,1.1941,1.2119,1.2229,1.2373,1.25,1.2596,1.2735,1.2886,1.3112,1.3298,1.3449,1.3624,1.3798,1.4,1.4157,1.4266,1.4477,1.4778,1.4926,1.5147,1.5291,1.5491,1.5685,1.5871,1.6053,1.6229,1.6423,1.6596,1.6759,1.7167,1.7324,1.7404,1.7604,1.7736,1.7875,1.8017,1.8246,1.8492,1.8794,1.9029,1.9259,1.9478,1.9799,2.0045,2.0327,2.0678,2.0895,2.1291,2.1621,2.2029,2.2359,2.2726,2.3403,2.3775,2.4139,2.4669,2.5435,2.6084,2.6578,2.7123,2.7656,2.8153,2.8919,2.9714,3.0373,3.139,3.2195,3.2927,3.3742,3.4784,3.6227,3.7471,3.869,3.9848,4.1475,4.3506,5.0239,5.6616,8.9947],"rec_yds|1":[-0.3842,-0.0959,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0445,0.0846,0.1004,0.1221,0.1356,0.1535,0.1652,0.175,0.1851,0.1931,0.2061,0.215,0.2224,0.2369,0.2458,0.2561,0.2635,0.2734,0.2864,0.293,0.3112,0.3209,0.33,0.3396,0.3485,0.3594,0.367,0.3811,0.3908,0.4007,0.4121,0.4186,0.4259,0.4377,0.4471,0.4529,0.4705,0.4773,0.4846,0.4947,0.5031,0.5081,0.5177,0.5257,0.5361,0.5423,0.549,0.556,0.5642,0.5732,0.5827,0.5956,0.6025,0.6131,0.6217,0.6299,0.6354,0.6414,0.653,0.6648,0.6772,0.6869,0.699,0.7073,0.722,0.7338,0.7462,0.754,0.7693,0.7796,0.7906,0.8001,0.8139,0.8236,0.8326,0.8391,0.8481,0.8578,0.8654,0.8727,0.8798,0.8874,0.8942,0.9033,0.9195,0.9273,0.9346,0.9491,0.9639,0.9713,0.9862,0.9962,1.0111,1.0253,1.0345,1.0459,1.0546,1.0628,1.0711,1.0867,1.093,1.1051,1.1198,1.1352,1.1465,1.155,1.1662,1.1844,1.2019,1.2133,1.231,1.2474,1.2583,1.2717,1.2941,1.3094,1.3233,1.3356,1.3524,1.3635,1.3777,1.3875,1.399,1.4097,1.4206,1.4495,1.4674,1.4885,1.5017,1.5125,1.5274,1.5483,1.5675,1.5902,1.6103,1.6174,1.6331,1.6466,1.6589,1.6789,1.7023,1.7282,1.7398,1.7578,1.776,1.8042,1.8379,1.8621,1.8944,1.9136,1.9357,1.9512,1.9849,2.0173,2.0425,2.0727,2.1116,2.1315,2.1626,2.1757,2.232,2.2843,2.3228,2.3719,2.4234,2.4666,2.5293,2.5938,2.6654,2.7398,2.7985,2.8832,2.9835,3.0703,3.2201,3.3463,3.4351,3.6042,3.8167,4.4148,6.2724],"rec|1":[0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.2623,0.2777,0.2832,0.2903,0.2984,0.3063,0.3161,0.3239,0.3307,0.3367,0.3445,0.3523,0.3612,0.3671,0.3717,0.3797,0.3837,0.3922,0.3994,0.4041,0.4116,0.4159,0.4234,0.4297,0.4365,0.4455,0.4511,0.4593,0.4689,0.475,0.4791,0.4891,0.4969,0.5064,0.5195,0.532,0.5451,0.5518,0.5584,0.5682,0.5756,0.5892,0.6016,0.6104,0.6204,0.6286,0.6399,0.6471,0.6587,0.6688,0.6805,0.6897,0.7022,0.7134,0.7244,0.7323,0.7528,0.7586,0.7674,0.7759,0.7816,0.7876,0.7928,0.8023,0.8112,0.8217,0.8265,0.8326,0.8387,0.8456,0.8517,0.8593,0.8656,0.8748,0.8805,0.8892,0.8959,0.9078,0.9132,0.9201,0.9268,0.9375,0.9481,0.9531,0.9628,0.9742,0.9833,0.9924,1.0012,1.011,1.0227,1.0295,1.0372,1.0463,1.0562,1.0665,1.0785,1.0898,1.1044,1.1163,1.1249,1.1322,1.1397,1.1493,1.1581,1.1656,1.1701,1.1804,1.1964,1.2012,1.2135,1.2221,1.2354,1.2408,1.2532,1.2657,1.2717,1.2835,1.2958,1.306,1.3126,1.3207,1.3313,1.3387,1.3451,1.3513,1.3632,1.3742,1.3832,1.3936,1.4038,1.4204,1.4321,1.446,1.4532,1.4623,1.4761,1.487,1.497,1.5092,1.5247,1.5368,1.5548,1.5704,1.5892,1.6075,1.6278,1.6411,1.6655,1.6856,1.7031,1.7293,1.7521,1.7695,1.782,1.7979,1.8198,1.8282,1.8445,1.8575,1.871,1.8903,1.9251,1.9485,1.978,1.9909,2.0173,2.0539,2.094,2.1287,2.1678,2.2119,2.2765,2.3108,2.3395,2.4153,2.4821,2.5754,2.6352,2.7371,2.8134,2.9752,3.1635,5.4484],"rec_yds|2":[-0.0872,-0.0357,0.0,0.0,0.0,0.0,0.0,0.0604,0.0899,0.1001,0.1193,0.1455,0.1601,0.1731,0.1882,0.2,0.2071,0.2196,0.2326,0.2466,0.2625,0.2807,0.2858,0.2999,0.3112,0.3237,0.3312,0.342,0.3514,0.3744,0.3837,0.395,0.4048,0.4102,0.421,0.4296,0.4448,0.4522,0.4605,0.4681,0.475,0.4798,0.4886,0.4938,0.5022,0.5039,0.5188,0.5268,0.5323,0.5409,0.5446,0.5528,0.5604,0.5743,0.5832,0.5958,0.6092,0.6135,0.6268,0.6332,0.6355,0.6396,0.6468,0.6591,0.664,0.671,0.6785,0.6837,0.6915,0.7014,0.7095,0.7133,0.7189,0.7241,0.7333,0.7367,0.7437,0.751,0.7562,0.7585,0.7644,0.7749,0.7813,0.7896,0.7986,0.8057,0.8141,0.8217,0.8288,0.8419,0.8497,0.8566,0.8648,0.8695,0.8742,0.8797,0.8834,0.8915,0.897,0.9043,0.9077,0.9142,0.9194,0.9297,0.9405,0.9439,0.9549,0.9668,0.9731,0.9842,0.9915,0.9986,1.0045,1.0097,1.0164,1.0241,1.0315,1.037,1.0436,1.0538,1.0585,1.0686,1.076,1.088,1.098,1.11,1.1233,1.1289,1.1397,1.1519,1.1611,1.1689,1.1794,1.1875,1.1953,1.2011,1.2115,1.2186,1.2293,1.2555,1.2659,1.2739,1.2883,1.2922,1.3009,1.3038,1.3174,1.3276,1.338,1.3423,1.367,1.3835,1.3918,1.4079,1.4182,1.4319,1.437,1.4434,1.4518,1.474,1.4846,1.5062,1.5174,1.5261,1.5435,1.5734,1.597,1.6076,1.626,1.6372,1.6571,1.6783,1.6976,1.7132,1.73,1.7489,1.7773,1.8031,1.8312,1.8503,1.8732,1.8841,1.9129,1.9364,1.9871,2.0205,2.053,2.0709,2.0989,2.1358,2.1606,2.1905,2.2152,2.2545,2.2777,2.4265,2.5129,2.6469,2.7499,2.9888,4.0944],"rec|2":[0.0,0.0,0.0,0.0,0.1684,0.1909,0.2016,0.2105,0.2196,0.2223,0.2296,0.238,0.2417,0.2461,0.2485,0.2918,0.3197,0.3402,0.3579,0.3671,0.3738,0.3889,0.4027,0.4121,0.4167,0.4265,0.4327,0.4431,0.4465,0.4562,0.4598,0.4691,0.4763,0.4786,0.4859,0.4897,0.4955,0.4996,0.5215,0.5318,0.5465,0.556,0.5703,0.5835,0.589,0.5973,0.6054,0.6126,0.62,0.6272,0.6362,0.6437,0.6541,0.6589,0.6684,0.6722,0.6782,0.6798,0.6845,0.6884,0.6952,0.6992,0.7042,0.7073,0.7133,0.7222,0.726,0.7333,0.7375,0.7433,0.7484,0.7583,0.7636,0.7697,0.7773,0.7841,0.7948,0.8023,0.8092,0.8219,0.8274,0.8346,0.8405,0.8466,0.8532,0.8631,0.8696,0.8723,0.8752,0.8828,0.8869,0.8909,0.8947,0.902,0.9083,0.9153,0.9245,0.9274,0.9338,0.9397,0.945,0.9506,0.9558,0.9599,0.9639,0.9665,0.9709,0.9768,0.981,0.9848,0.9882,0.9903,0.9956,1.0082,1.017,1.0251,1.0362,1.0422,1.0561,1.0633,1.0661,1.0715,1.0793,1.0849,1.0875,1.0908,1.0959,1.1082,1.1139,1.124,1.1345,1.1422,1.1517,1.1649,1.1713,1.1767,1.1831,1.188,1.1953,1.1981,1.2007,1.2079,1.2139,1.2228,1.2297,1.2364,1.243,1.2497,1.2564,1.264,1.27,1.2798,1.2967,1.3061,1.3166,1.3249,1.3393,1.3525,1.3557,1.3694,1.3785,1.3876,1.3939,1.4015,1.4155,1.4276,1.4371,1.4435,1.4505,1.4643,1.4814,1.4957,1.5083,1.5298,1.567,1.5869,1.6015,1.6275,1.6369,1.6503,1.6591,1.6718,1.6921,1.7035,1.7363,1.7661,1.7904,1.8241,1.8434,1.8919,1.9092,1.936,1.9827,2.044,2.0987,2.1261,2.1536,2.1766,2.2166,2.4155,2.9729],"rush_yds|2":[-0.0178,0.0465,0.0521,0.0635,0.0866,0.1218,0.159,0.168,0.1992,0.2135,0.2348,0.252,0.2696,0.2829,0.3007,0.3104,0.3181,0.3259,0.3322,0.3343,0.3366,0.3511,0.3549,0.3703,0.3738,0.384,0.3879,0.4121,0.4215,0.4338,0.4434,0.4543,0.4552,0.4641,0.4701,0.4774,0.4878,0.4967,0.499,0.5027,0.5057,0.5205,0.5309,0.5487,0.5548,0.5563,0.56,0.5655,0.577,0.5847,0.5883,0.5897,0.5979,0.6082,0.6108,0.6165,0.6222,0.6282,0.6304,0.6381,0.6498,0.6575,0.6654,0.6747,0.679,0.6947,0.6975,0.7135,0.7232,0.7283,0.7319,0.7359,0.7483,0.7544,0.7583,0.7672,0.774,0.778,0.784,0.7885,0.7975,0.8028,0.8107,0.8153,0.8212,0.827,0.8415,0.8481,0.8492,0.8581,0.8606,0.8678,0.8747,0.8777,0.8805,0.885,0.8901,0.8986,0.9053,0.9231,0.9253,0.9319,0.9417,0.9545,0.963,0.9752,0.9808,0.9863,1.0004,1.0061,1.0113,1.0163,1.0186,1.0252,1.0324,1.0415,1.0459,1.0513,1.0773,1.0853,1.0946,1.1038,1.1149,1.119,1.124,1.1449,1.1492,1.1507,1.1578,1.1844,1.1906,1.2006,1.2024,1.21,1.2146,1.2209,1.2284,1.2377,1.2396,1.2444,1.2672,1.2688,1.2746,1.2805,1.2868,1.2894,1.3032,1.3263,1.3378,1.346,1.3536,1.356,1.3648,1.3741,1.3862,1.3907,1.4037,1.4114,1.4251,1.4329,1.4426,1.4519,1.4565,1.4745,1.4913,1.4983,1.5088,1.5187,1.5322,1.5377,1.5473,1.5584,1.5644,1.5771,1.594,1.6079,1.6202,1.6294,1.6447,1.6618,1.6927,1.7318,1.7324,1.7507,1.7618,1.8389,1.8518,1.903,1.9213,1.9648,1.9732,1.989,2.0629,2.1506,2.1774,2.2431,2.458,2.5221,2.5805,2.7501,3.2411],"rush_att|2":[0.0806,0.1272,0.2016,0.3225,0.3322,0.3452,0.3625,0.369,0.3846,0.3998,0.4199,0.428,0.4431,0.4632,0.4704,0.4878,0.4986,0.5015,0.514,0.5205,0.5246,0.5445,0.5504,0.558,0.5635,0.5891,0.6048,0.6051,0.6101,0.6354,0.6399,0.6478,0.6569,0.6618,0.6677,0.6776,0.6836,0.6845,0.6875,0.6945,0.7006,0.7017,0.7053,0.708,0.7175,0.7289,0.7329,0.737,0.7437,0.7508,0.7524,0.7555,0.7574,0.759,0.7611,0.7644,0.7653,0.7699,0.7807,0.782,0.785,0.7893,0.7971,0.8029,0.8087,0.8112,0.8125,0.8148,0.8201,0.8233,0.8272,0.831,0.8367,0.8381,0.8414,0.8494,0.8559,0.8617,0.8722,0.8738,0.8785,0.8827,0.8844,0.8904,0.8935,0.895,0.8965,0.9043,0.9056,0.9083,0.9129,0.9212,0.9257,0.9348,0.9374,0.9394,0.9495,0.9557,0.972,0.976,0.9828,0.9922,0.9967,1.0015,1.003,1.0042,1.0059,1.0121,1.0137,1.0206,1.0265,1.0325,1.0349,1.0384,1.041,1.0427,1.0444,1.0494,1.0523,1.0565,1.062,1.0691,1.0797,1.0842,1.0998,1.1005,1.1122,1.1166,1.1227,1.1316,1.1331,1.1366,1.1406,1.1486,1.1508,1.1531,1.1623,1.1667,1.1746,1.1802,1.1867,1.1878,1.2102,1.2166,1.2232,1.2267,1.231,1.2367,1.2391,1.2461,1.2553,1.2576,1.2681,1.2736,1.2791,1.282,1.2938,1.3055,1.3088,1.3173,1.321,1.3286,1.3354,1.3375,1.3457,1.3475,1.3545,1.3646,1.3717,1.3791,1.3904,1.3936,1.4121,1.4138,1.4193,1.4271,1.4352,1.4462,1.4517,1.4559,1.4712,1.4807,1.4928,1.4974,1.5049,1.5409,1.5539,1.5623,1.5813,1.6081,1.6277,1.6359,1.6545,1.7002,1.7151,1.7465,1.7822,1.817,1.841,1.98,2.192],"rush_yds|1":[-0.2811,-0.0613,-0.0303,0.0,0.0,0.0,0.0,0.0268,0.0549,0.0657,0.0764,0.0848,0.0977,0.1059,0.1181,0.1416,0.1533,0.1587,0.1773,0.1836,0.1937,0.2078,0.227,0.2371,0.2522,0.2597,0.2637,0.2739,0.2778,0.2932,0.2973,0.3127,0.3209,0.3322,0.3518,0.3596,0.3681,0.3726,0.3803,0.3911,0.402,0.4125,0.4209,0.434,0.4409,0.4439,0.4553,0.4606,0.4673,0.4817,0.4878,0.4924,0.4982,0.511,0.5319,0.5345,0.5376,0.5498,0.5588,0.5754,0.5825,0.5937,0.6049,0.6122,0.6243,0.6295,0.6395,0.6472,0.6538,0.6653,0.6725,0.6814,0.685,0.6882,0.6967,0.7067,0.7279,0.7332,0.7403,0.745,0.7498,0.7568,0.7618,0.7735,0.7774,0.7926,0.7993,0.8018,0.8131,0.8241,0.8279,0.8359,0.8473,0.855,0.8642,0.87,0.8849,0.8886,0.8973,0.902,0.9213,0.9302,0.9386,0.9495,0.9609,0.9703,0.9813,0.9915,1.0018,1.0125,1.0291,1.0387,1.0416,1.0537,1.059,1.0633,1.0711,1.0822,1.0972,1.0994,1.1122,1.1251,1.1341,1.1466,1.1551,1.1768,1.1825,1.1863,1.2054,1.2101,1.2129,1.2222,1.2369,1.2515,1.2587,1.2666,1.2776,1.2904,1.2979,1.3005,1.3107,1.3222,1.3456,1.3515,1.3737,1.3852,1.3905,1.4033,1.4109,1.4247,1.4464,1.4537,1.4606,1.482,1.492,1.504,1.5141,1.53,1.5505,1.5594,1.5686,1.5928,1.6104,1.6289,1.6429,1.6636,1.6783,1.7186,1.7458,1.787,1.8181,1.8386,1.8773,1.8937,1.9088,1.9396,1.9743,2.0005,2.0408,2.0803,2.1061,2.1137,2.1618,2.2145,2.2406,2.2788,2.3253,2.3723,2.3971,2.4485,2.4872,2.558,2.6132,2.707,2.833,2.9068,3.0937,3.2668,3.5899,3.8945,5.7097],"rush_att|1":[0.0,0.0,0.0,0.0972,0.1307,0.1445,0.1568,0.1653,0.1929,0.2243,0.233,0.2555,0.2763,0.2837,0.2892,0.3017,0.3099,0.3172,0.3223,0.3319,0.3501,0.3687,0.388,0.3967,0.404,0.4155,0.4262,0.4449,0.4484,0.456,0.4666,0.4734,0.4774,0.4823,0.4867,0.4906,0.4998,0.5135,0.5219,0.5326,0.541,0.5496,0.5633,0.5734,0.5927,0.5998,0.6082,0.6182,0.6313,0.6358,0.6427,0.6521,0.6629,0.6815,0.6921,0.7001,0.7101,0.7179,0.7379,0.7411,0.7461,0.7537,0.76,0.7646,0.7717,0.7734,0.7758,0.7801,0.7834,0.7938,0.7975,0.8029,0.8095,0.8135,0.8211,0.8268,0.8353,0.8481,0.8542,0.8621,0.8659,0.8729,0.8774,0.8823,0.8921,0.9014,0.9114,0.9152,0.9235,0.9253,0.9282,0.934,0.9374,0.9488,0.9564,0.9618,0.9682,0.9711,0.9824,0.9849,0.9922,0.9994,1.006,1.0174,1.0239,1.0313,1.0443,1.0536,1.0653,1.0694,1.0811,1.086,1.0939,1.1021,1.1049,1.111,1.1185,1.1263,1.1368,1.1458,1.1547,1.1639,1.1765,1.1783,1.1818,1.1922,1.204,1.2128,1.2161,1.2213,1.2279,1.236,1.2456,1.2521,1.262,1.2717,1.2771,1.2864,1.294,1.2963,1.3093,1.3117,1.3283,1.336,1.3403,1.349,1.3545,1.3706,1.3791,1.3955,1.3998,1.4157,1.4286,1.4315,1.4352,1.4455,1.4614,1.4662,1.4763,1.4889,1.4971,1.5103,1.5157,1.5237,1.526,1.5436,1.5458,1.5544,1.5617,1.5758,1.5785,1.5839,1.6145,1.6254,1.6331,1.6418,1.6647,1.6731,1.7052,1.7319,1.7396,1.7599,1.7786,1.8098,1.8537,1.8686,1.9022,1.9294,1.974,1.9956,2.0565,2.0865,2.1399,2.1591,2.2443,2.3082,2.375,2.495,2.774,2.9458,3.5523]}
# P(over) is pulled 25% toward 50%: in backtests the raw probabilities ran a little hot at the extremes.
P_SHRINK = 0.75


def model_games(games_raw, seasons):
    out = []
    for g in games_raw:
        if int(g["season"]) not in seasons or g["game_type"] != "REG":
            continue
        out.append({"id": g["game_id"], "season": int(g["season"]), "week": int(g["week"]), "day": g["gameday"],
                    "home": g["home_team"], "away": g["away_team"],
                    "hs": to_int(g["home_score"]) if g["home_score"] else None,
                    "as": to_int(g["away_score"]) if g["away_score"] else None,
                    "spread": to_num(g["spread_line"]), "total": to_num(g["total_line"]),
                    "hqb_id": g["home_qb_id"], "aqb_id": g["away_qb_id"],
                    "hqb": g["home_qb_name"], "aqb": g["away_qb_name"]})
    return out


def build_td(season, games_raw, stats_raw, display_names):
    print("Downloading play-by-play for the touchdown model…")
    history = sorted({season - k for k in HISTORY_WEIGHTS} | {season})
    plays = {}
    for s in history:
        cache = f"pbp_{s}.csv.gz" if s < season else None
        blob = get_bytes(PBP_URL.format(season=s), cache)
        plays[s] = list(read_pbp(io.BytesIO(blob))) if blob else []
    if not any(plays.values()):
        return {}, {}, {}, None

    # Birth dates and positions for every player (used for the age curve), plus headshot photos
    positions, births, headshots, pfr_to_gsis, draft = {}, {}, {}, {}, {}
    today_cache = f"players_{datetime.now(ET).date().isoformat()}.csv"
    for old in CACHE.glob("players_*.csv") if CACHE.exists() else []:
        if old.name != today_cache:
            old.unlink()
    pblob = get_bytes(PLAYERS_URL, today_cache)
    for r in csv.DictReader(io.StringIO(pblob.decode("utf-8"))) if pblob else []:
        pos = POS_MAP.get(r["position"])
        if pos and r["gsis_id"]:
            positions[r["gsis_id"]] = pos
            births[r["gsis_id"]] = r["birth_date"]
            display_names.setdefault(r["gsis_id"], r["display_name"])
            if r.get("headshot"):
                headshots[r["gsis_id"]] = r["headshot"]
        if r["gsis_id"] and r.get("pfr_id"):
            pfr_to_gsis[r["pfr_id"]] = r["gsis_id"]
        if r["gsis_id"] and r.get("rookie_season"):
            try:
                draft[r["gsis_id"]] = (int(r["draft_round"]) if r.get("draft_round") not in ("", "NA", None) else None,
                                       int(r["rookie_season"]))
            except ValueError:
                pass

    prev = get_bytes(STATS_URL.format(season=season - 1), f"stats_player_week_{season - 1}.csv")
    for rows in ((list(csv.DictReader(io.StringIO(prev.decode("utf-8")))) if prev else []), stats_raw):
        for r in rows:
            pos = POS_MAP.get(r["position"])
            if pos:
                positions[r["player_id"]] = pos
                display_names.setdefault(r["player_id"], r["player_display_name"] or r["player_name"])

    # Official injury reports: Out and Doubtful players are removed and their share goes to teammates.
    injuries = defaultdict(dict)
    for r in get_csv(INJ_URL.format(season=season)) or []:
        if r["game_type"] == "REG" and r["report_status"]:
            injuries[(int(r["week"]), r["team"])][r["gsis_id"]] = {
                "name": r["full_name"], "pos": r["position"], "status": r["report_status"],
                "injury": r["report_primary_injury"], "practice": r["practice_status"]}

    games = model_games(games_raw, tuple(history))
    injury_notes = {}
    for g in games:
        if g["season"] != season:
            continue
        rep = {**injuries.get((g["week"], g["home"]), {}), **injuries.get((g["week"], g["away"]), {})}
        g["out"] = {pid for pid, x in rep.items() if x["status"] in ("Out", "Doubtful")}
        g["injury_report"] = rep
        g["questionable"] = {pid: ("dnp" if "Did Not" in (x["practice"] or "") else "limited" if "Limited" in (x["practice"] or "")
                                   else "full" if "Full" in (x["practice"] or "") else None)
                             for pid, x in rep.items() if x["status"] == "Questionable"}
        g["questionable"] = {k: v for k, v in g["questionable"].items() if v}
    # Snap counts: each player's share of his team's offensive snaps, per game
    snaps, def_snaps = {}, defaultdict(list)
    day_of_game = {g["game_id"]: g["gameday"] for g in games_raw}
    for s_ in history:
        blob = get_bytes(SNAPS_URL.format(season=s_), f"snap_counts_{s_}.csv" if s_ < season else None)
        for r in csv.DictReader(io.StringIO(blob.decode("utf-8"))) if blob else []:
            gid_ = pfr_to_gsis.get(r["pfr_player_id"])
            if gid_ and r["offense_pct"]:
                snaps[(r["game_id"], gid_)] = float(r["offense_pct"])
            if gid_ and r["defense_pct"] and float(r["defense_pct"]) > 0 and r["game_id"] in day_of_game:
                def_snaps[gid_].append((day_of_game[r["game_id"]], float(r["defense_pct"])))
    for v in def_snaps.values():
        v.sort()
    # Defenders ruled out (Out/Doubtful) for each game, and head coaches by season
    def_out = {}
    for g in games:
        if g["season"] == season:
            def_out[g["id"]] = {t: [(pid, x["pos"]) for pid, x in injuries.get((g["week"], t), {}).items()
                                    if x["status"] in ("Out", "Doubtful") and x["pos"] in DB_POS | FRONT_POS]
                                for t in (g["home"], g["away"])}
    coaches = {}
    for g in games_raw:
        coaches[(int(g["season"]), g["home_team"])] = g["home_coach"]
        coaches[(int(g["season"]), g["away_team"])] = g["away_coach"]
    # Weather: measured conditions for played games, kickoff forecasts for upcoming outdoor games
    forecasts = fetch_forecasts(games_raw)
    weather = {}
    for g in games_raw:
        f = forecasts.get(g["game_id"])
        weather[g["game_id"]] = {"covered": covered(g["roof"]),
                                 "wind": f["wind"] if f else to_num(g["wind"]),
                                 "temp": f["temp"] if f else to_num(g["temp"]),
                                 "pop": f["pop"] if f else None, "forecast": bool(f)}
    model = TDModel(plays, games, positions, season, births, snaps, coaches)

    # Career context: last season's TDs vs expected TDs, and age now
    last = defaultdict(lambda: [0, 0, 0.0])  # games, TDs, xTD
    seen = set()
    for (gid, pid), pg in model.player_games.items():
        if model.games.get(gid, {}).get("season") == season - 1:
            if (gid, pid) not in seen:
                seen.add((gid, pid)); last[pid][0] += 1
            last[pid][1] += pg["td"]; last[pid][2] += pg["x_rush"] + pg["x_rec"]

    def age_now(pid):
        b = births.get(pid)
        if not b:
            return None
        by, bm, bd = (int(x) for x in b.split("-")[:3])
        t = datetime.now(ET).date()
        return t.year - by - ((t.month, t.day) < (bm, bd))
    global USE_MATCHUP
    preds, hits = {}, {}
    for g in games:
        if g["season"] != season:
            continue
        rows = []
        USE_MATCHUP = False
        neutral = {r["pid"]: r["prob"] for r in model.predict_game(g)}
        USE_MATCHUP = True
        for r in model.predict_game(g):
            if r["prob"] < 0.02:
                continue
            rows.append({
                "pid": r["pid"], "name": display_names.get(r["pid"], r["name"]), "team": r["team"],
                "pos": r["pos"], "p": round(r["prob"], 4),
                "lr": round(r["lam_rush"], 4), "lc": round(r["lam_rec"], 4),
                "rs": round(r["rush_share"], 3), "cs": round(r["rec_share"], 3),
                "tt": round(r["team_tds"], 2), "imp": round(r["implied"], 1) if r["implied"] else None,
                "rz": [r["rz_car"], r["rz_tgt"], r["i10_car"], r["i10_tgt"]],
                "mx": round(r["prob"] - neutral.get(r["pid"], r["prob"]), 4),
                "td": r["td"], "xtd": round(r["xtd"], 2), "g": r["games"],
                "miss": r["missed_last"], "fill": r["fill_in"],
                "car": [age_now(r["pid"]), *last[r["pid"]][:2], round(last[r["pid"]][2], 1),
                        round(age_factor(r["pos"], births.get(r["pid"]), season - 1, season), 3)],
                "inj": ([g["injury_report"][r["pid"]]["status"], g["injury_report"][r["pid"]]["injury"]]
                        if r["pid"] in g.get("injury_report", {}) else None),
            })
        preds[g["id"]] = sorted(rows, key=lambda x: -x["p"])
        ruled = [[x["name"], team_of, x["pos"], x["status"], x["injury"]]
                 for team_of in (g["away"], g["home"])
                 for pid, x in injuries.get((g["week"], team_of), {}).items()
                 if x["status"] in ("Out", "Doubtful") and positions.get(pid)]
        if ruled:
            injury_notes[g["id"]] = ruled
    for p in plays[season]:
        if p["td"]:
            hits.setdefault(p["gid"], []).append(p["pid"])
    for r in stats_raw:
        if r.get("headshot_url") and r["player_id"] not in headshots:
            headshots[r["player_id"]] = r["headshot_url"]
    ctx = {"games": games, "births": births, "positions": positions, "headshots": headshots,
           "snaps": snaps, "weather": weather, "def_snaps": def_snaps, "def_out": def_out, "coaches": coaches, "draft": draft}
    return preds, hits, injury_notes, ctx



# ---------------------------------------------------------------------------
# Sportsbook odds (The Odds API, https://the-odds-api.com). Free keys include
# 500 credits a month; each game costs about 5 credits (anytime TD + 4 yardage/volume markets).
# ---------------------------------------------------------------------------
ODDS_BASE = "https://api.the-odds-api.com/v4/sports/americanfootball_nfl"
BOOK_NAMES = {"hardrockbet_fl": "Hard Rock Bet (FL)", "hardrockbet": "Hard Rock Bet",
              "hardrockbet_az": "Hard Rock Bet (AZ)", "hardrockbet_oh": "Hard Rock Bet (OH)"}


def norm_name(name):
    import unicodedata
    n = unicodedata.normalize("NFKD", name or "").encode("ascii", "ignore").decode().lower()
    n = "".join(c if c.isalnum() or c == " " else " " for c in n)
    parts = [w for w in n.split() if w not in ("jr", "sr", "ii", "iii", "iv", "v")]
    return " ".join(parts)


PROP_MARKETS = {"player_reception_yds": "rec_yds", "player_receptions": "rec",
                "player_rush_yds": "rush_yds", "player_rush_attempts": "rush_att"}
ALL_MARKETS = ["player_anytime_td", *PROP_MARKETS]


def fetch_book_odds(api_key, book, games, teams, days, only_date=None):
    """Return ({gid: {"td": {norm: {price, name}}, "props": {stat: {norm: {name, line, over, under}}}}}, message).
    Costs about one Odds API credit per market per game (5 markets)."""
    resp = requests.get(f"{ODDS_BASE}/events", params={"apiKey": api_key}, timeout=30)
    if resp.status_code == 401:
        return {}, "Odds API key was rejected. Check the key and try again."
    resp.raise_for_status()
    by_matchup = {(teams.get(g["home"], [g["home"]])[0], teams.get(g["away"], [g["away"]])[0], g["day"]): g["id"]
                  for g in games}
    now = datetime.now(ET)
    out, remaining, fetched = {}, None, 0
    for ev in resp.json():
        start = datetime.fromisoformat(ev["commence_time"].replace("Z", "+00:00")).astimezone(ET)
        if only_date and start.date().isoformat() != only_date:
            continue
        if not only_date and (start - now).days > days:
            continue
        gid = by_matchup.get((ev["home_team"], ev["away_team"], start.date().isoformat()))
        if not gid:
            continue
        r = requests.get(f"{ODDS_BASE}/events/{ev['id']}/odds", timeout=30, params={
            "apiKey": api_key, "bookmakers": book, "markets": ",".join(ALL_MARKETS), "oddsFormat": "american"})
        remaining = r.headers.get("x-requests-remaining", remaining)
        if r.status_code == 429:
            return out, "Out of Odds API credits for this month; showing what was fetched."
        if r.status_code != 200:
            continue
        fetched += 1
        entry = {"td": {}, "props": {}}
        for bm in r.json().get("bookmakers", []):
            for m in bm.get("markets", []):
                key = m.get("key")
                for o in m.get("outcomes", []):
                    player, side, price = o.get("description") or o.get("name"), o.get("name"), o.get("price")
                    if not player or price is None:
                        continue
                    if key == "player_anytime_td":
                        if side not in ("No", "Under"):
                            entry["td"][norm_name(player)] = {"price": int(price), "name": player}
                    elif key in PROP_MARKETS and side in ("Over", "Under") and o.get("point") is not None:
                        slot = entry["props"].setdefault(PROP_MARKETS[key], {}).setdefault(
                            norm_name(player), {"name": player, "line": float(o["point"]), "over": None, "under": None})
                        if float(o["point"]) == slot["line"]:
                            slot["over" if side == "Over" else "under"] = int(price)
        if entry["td"] or entry["props"]:
            out[gid] = entry
    msg = f"Fetched {BOOK_NAMES.get(book, book)} player props for {len(out)} of {fetched} games checked"
    if remaining is not None:
        msg += f"; {remaining} Odds API credits left this month"
    return out, msg + "."


def attach_odds(td, odds):
    """Put each anytime-TD price on the matching model row; return players the book lists but the model doesn't."""
    book_only = {}
    for gid, prices in odds.items():
        rows = td.get(gid, [])
        by_name = {norm_name(r["name"]): r for r in rows}
        for key, o in prices.items():
            if key in by_name:
                by_name[key]["book"] = o["price"]
            else:
                book_only.setdefault(gid, []).append([o["name"], o["price"]])
    return book_only


def attach_prop_odds(props, odds):
    """{gid: {pid: {stat: [line, over, under]}}} for players the book lists."""
    out = {}
    for gid, by_stat in odds.items():
        by_name = {norm_name(r["name"]): r["pid"] for r in props.get(gid, [])}
        for stat, players in by_stat.items():
            for key, o in players.items():
                pid = by_name.get(key)
                if pid:
                    out.setdefault(gid, {}).setdefault(pid, {})[stat] = [o["line"], o["over"], o["under"]]
    return out


def _recent_snaps(snaps, games_played, day, pid):
    """Average share of offensive snaps over a player's last three games before `day`."""
    xs = [snaps.get((gid, pid)) for d, gid in sorted(games_played) if d < day][-3:]
    xs = [x for x in xs if x is not None]
    return round(sum(xs) / len(xs), 3) if xs else None


def build_props(season, stats_raw, ctx, display_names):
    """Yardage and volume projections for every game this season (each from games before it)."""
    rows = []
    for s in sorted({season - k for k in HISTORY_WEIGHTS} | {season}):
        if s == season:
            raw = stats_raw
        else:
            blob = get_bytes(STATS_URL.format(season=s), f"stats_player_week_{s}.csv")
            raw = list(csv.DictReader(io.StringIO(blob.decode("utf-8")))) if blob else []
        for r in raw:
            pos = POS_MAP.get(r["position"])
            if not pos or r["season_type"] != "REG":
                continue
            rows.append({"season": int(r["season"]), "gid": r["game_id"], "team": r["team"], "opp": r["opponent_team"],
                         "pid": r["player_id"], "name": display_names.get(r["player_id"], r["player_display_name"]),
                         "pos": pos, "tgt": to_int(r["targets"]), "rec": to_int(r["receptions"]),
                         "rec_yds": to_int(r["receiving_yards"]), "car": to_int(r["carries"]),
                         "rush_yds": to_int(r["rushing_yards"]),
                         "att": to_int(r["attempts"]) if pos == "QB" else 0,
                         "cmp": to_int(r["completions"]) if pos == "QB" else 0,
                         "pyd": to_int(r["passing_yards"]) if pos == "QB" else 0})
    games = {g["id"]: g for g in ctx["games"]}
    positions = {**{r["pid"]: r["pos"] for r in rows}, **ctx["positions"]}
    births = ctx["births"]
    model = PropsModel(rows, games, season, HISTORY_WEIGHTS,
                       lambda pos, pid, a, b: age_factor(pos, births.get(pid), a, b), positions,
                       ctx.get("snaps"), ctx.get("weather"), ctx.get("coaches"), None,
                       ctx.get("def_snaps"), ctx.get("def_out"), ctx.get("draft"))
    snaps = ctx.get("snaps", {})
    played = defaultdict(list)  # (pid, team) -> [(day, gid)] this season
    for r in rows:
        if r["season"] == season and r["gid"] in games:
            played[(r["pid"], r["team"])].append((games[r["gid"]]["day"], r["gid"]))
    actual = {(r["gid"], r["pid"]): r for r in rows if r["season"] == season}
    rnd = lambda v, d=2: None if v is None else round(v, d)
    out = {}
    for g in games.values():
        if g["season"] != season:
            continue
        rep = g.get("injury_report", {})
        res = []
        for pr in model.predict_game(g, frozenset(g.get("out", set()))):
            mu = pr["proj"]
            if (mu["rec_yds"] or 0) < 5 and (mu["rush_att"] or 0) < 2:
                continue
            a = actual.get((g["id"], pr["pid"]))
            res.append({
                "pid": pr["pid"], "name": pr["name"], "team": pr["team"], "pos": pr["pos"],
                "mu": [rnd(mu["rec_yds"]), rnd(mu["rec"]), rnd(mu["rush_yds"]), rnd(mu["rush_att"])],
                "tgt": rnd(pr["tgt"]), "car": rnd(pr["car"]), "ts": rnd(pr["tshare"], 3), "cs": rnd(pr["cshare"], 3),
                "avg": [rnd(pr["avg"][k], 1) for k in ("rec_yds", "rec", "rush_yds", "rush_att")],
                "l3": [rnd(pr["l3"][k], 1) for k in ("rec_yds", "rec", "rush_yds", "rush_att")],
                "log": pr["log"], "oe": [rnd(pr["opp_eff"][k], 3) for k in ("ypt", "catch", "ypc")],
                "n": pr["n"],
                "sn": _recent_snaps(snaps, played.get((pr["pid"], pr["team"]), []), g["day"], pr["pid"]),
                "inj": [rep[pr["pid"]]["status"], rep[pr["pid"]]["injury"]] if pr["pid"] in rep else None,
                "act": [a["rec_yds"], a["rec"], a["rush_yds"], a["car"]] if a else None,
            })
        out[g["id"]] = res
    return out


def build_data(season, odds_key=None, book="hardrockbet_fl", odds_days=7, odds_date=None, fetch_odds=True):
    games_raw = get_csv(GAMES_URL)
    teams_raw = get_csv(TEAMS_URL)
    stats_raw = get_csv(STATS_URL.format(season=season)) or []

    games = []
    for g in games_raw:
        if g["season"] != str(season):
            continue
        games.append({
            "id": g["game_id"], "week": int(g["week"]), "type": g["game_type"],
            "day": g["gameday"], "time": g["gametime"],
            "away": g["away_team"], "home": g["home_team"],
            "as": to_int(g["away_score"]) if g["away_score"] else None,
            "hs": to_int(g["home_score"]) if g["home_score"] else None,
            "spread": to_num(g["spread_line"]), "total": to_num(g["total_line"]),
            "stadium": g["stadium"], "roof": g["roof"],
            "temp": to_num(g["temp"]), "wind": to_num(g["wind"]),
            "aqb": g["away_qb_name"], "hqb": g["home_qb_name"],
        })
    games.sort(key=lambda g: (g["day"], g["time"]))
    day_of = {g["id"]: g["day"] for g in games}

    # Latest name/logo per team abbreviation (current season wins).
    teams = {}
    for t in sorted(teams_raw, key=lambda t: t["season"]):
        if int(t["season"]) <= season:
            logo = f"https://a.espncdn.com/i/teamlogos/nfl/500/{t['espn'].lower()}.png" if t["espn"] else ""
            teams[t["team"]] = [t["full"], logo]

    players, rows = {}, []
    for r in stats_raw:
        pos = POS_MAP.get(r["position"])
        if not pos or r["season_type"] != "REG" or r["game_id"] not in day_of:
            continue
        players[r["player_id"]] = [r["player_display_name"] or r["player_name"], pos]
        rows.append([day_of[r["game_id"]], r["game_id"], r["team"], r["opponent_team"], r["player_id"]]
                    + [to_int(r[c]) for c in STAT_COLS])
    rows.sort(key=lambda r: r[0])

    names = {pid: v[0] for pid, v in players.items()}
    td, td_hits, injury_notes, ctx = build_td(season, games_raw, stats_raw, names)
    print("Projecting yards, receptions and rush attempts…")
    props = build_props(season, stats_raw, ctx, names) if ctx else {}

    # Sportsbook odds: fetch the requested games, then merge into a cache so earlier fetches stick.
    status = ""
    odds_cache_path = CACHE / f"odds_{season}_{book}.json"
    try:
        odds_cache = json.loads(odds_cache_path.read_text()) if odds_cache_path.exists() else {}
    except ValueError:
        odds_cache = {}
    if odds_key and fetch_odds:
        print(f"Downloading {BOOK_NAMES.get(book, book)} odds…")
        try:
            odds, status = fetch_book_odds(odds_key, book, games, teams, odds_days, odds_date)
            stamp = datetime.now(ET).isoformat()
            for gid, entry in odds.items():
                odds_cache[gid] = {"fetched": stamp, "prices": entry["td"], "props": entry["props"]}
            CACHE.mkdir(exist_ok=True)
            odds_cache_path.write_text(json.dumps(odds_cache))
        except requests.RequestException as e:
            status = f"Couldn't reach The Odds API ({e}); kept the last odds you loaded."
        print(status)
    book_only = attach_odds(td, {gid: v.get("prices", {}) for gid, v in odds_cache.items()})
    prop_odds = attach_prop_odds(props, {gid: v.get("props", {}) for gid, v in odds_cache.items()})
    odds_times = {gid: v["fetched"] for gid, v in odds_cache.items()}
    book_info = {"name": BOOK_NAMES.get(book, book), "key": book} if odds_cache else None

    nhl = None
    if nhl_props is not None:
        try:
            nhl = nhl_props.build(odds_key, book, odds_date, fetch_odds)
            if nhl.get("status"):
                status = (status + " " + nhl["status"]).strip()
        except Exception as e:  # never let the NHL tab break the NFL board
            print(f"NHL data failed: {e}")
            nhl = {"error": str(e)}

    return {
        "season": season, "nhl": nhl,
        "td": td, "tdHits": td_hits, "injuries": injury_notes, "book": book_info, "bookOnly": book_only,
        "oddsTimes": odds_times, "status": status,
        "props": props, "propOdds": prop_odds, "ratioQ": RATIO_Q, "pShrink": P_SHRINK,
        "heads": {pid: url for pid, url in (ctx or {}).get("headshots", {}).items()
                  if pid in {r["pid"] for rows_ in list(td.values()) + list(props.values()) for r in rows_}},
        "generated": datetime.now(ET).strftime("%b %d, %Y at %I:%M %p ET").replace(" 0", " "),
        "hasPlayerStats": bool(rows),
        "games": games, "teams": teams, "players": players, "pw": rows,
    }


CONFIG = Path(__file__).resolve().parent / "nfl_board_config.json"  # your saved Odds API key and book


def load_config():
    try:
        return json.loads(CONFIG.read_text())
    except (OSError, ValueError):
        return {}


def save_config(cfg):
    CONFIG.write_text(json.dumps(cfg, indent=2))


def write_board(data, out):
    blob = json.dumps(data, separators=(",", ":")).replace("</", "<\\/")
    tmp = out.with_name(out.name + ".part")   # write then swap, so the open board never sees a half-written file
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp.write_text(TEMPLATE.replace("__DATA__", blob), encoding="utf-8")
    os.replace(tmp, out)


def serve(season, out, port, open_browser):
    """Run the board at http://localhost:PORT with working Refresh and saved-key support."""
    import threading
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

    lock = threading.Lock()

    def rebuild(date=None, book=None, fetch_odds=True):
        cfg = load_config()
        book = book or cfg.get("book", "hardrockbet_fl")
        data = build_data(season, cfg.get("odds_key"), book, 7, date, fetch_odds)
        write_board(data, out)
        return data.get("status") or ""

    if not out.exists():
        print("Building the board for the first time…")
        rebuild(fetch_odds=False)

    class Handler(BaseHTTPRequestHandler):
        def _local(self):
            host = (self.headers.get("Host") or "").split(":")[0]
            return host in ("localhost", "127.0.0.1")

        def _send(self, code, body, ctype="application/json"):
            data = body if isinstance(body, bytes) else json.dumps(body).encode()
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            if not self._local():
                return self._send(403, {"error": "local only"})
            path = self.path.split("?")[0]
            if path in ("/", "/index.html"):
                return self._send(200, out.read_bytes(), "text/html; charset=utf-8")
            if path == "/api/status":
                cfg = load_config()
                return self._send(200, {"served": True, "hasKey": bool(cfg.get("odds_key")),
                                        "book": cfg.get("book", "hardrockbet_fl")})
            self._send(404, {"error": "not found"})

        def do_POST(self):
            if not self._local():
                return self._send(403, {"error": "local only"})
            try:
                body = json.loads(self.rfile.read(int(self.headers.get("Content-Length") or 0)) or b"{}")
            except ValueError:
                body = {}
            if self.path == "/api/settings":
                cfg = load_config()
                if "odds_key" in body:
                    cfg["odds_key"] = (body["odds_key"] or "").strip()
                if body.get("book") in BOOK_NAMES:
                    cfg["book"] = body["book"]
                save_config(cfg)
                return self._send(200, {"ok": True, "hasKey": bool(cfg.get("odds_key"))})
            if self.path == "/api/refresh":
                with lock:
                    try:
                        msg = rebuild(body.get("date"), body.get("book"), bool(body.get("odds", True)))
                        return self._send(200, {"ok": True, "message": msg})
                    except Exception as e:  # report any download or build problem to the page
                        return self._send(500, {"ok": False, "message": f"Refresh failed: {e}"})
            self._send(404, {"error": "not found"})

        def log_message(self, *args):
            pass

    url = f"http://localhost:{port}/"
    try:
        server = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    except OSError:
        print(f"The board is already running at {url} (opening it). To restart, close the other window first.")
        if open_browser:
            webbrowser.open(url)
        return
    print(f"NFL Game Day Board is running at {url}  (leave this window open; Ctrl+C to stop)")
    if open_browser:
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("Stopped.")


def _log_to_file(path):
    """Send prints and errors to a log file (the automatic update runs with no window). Keeps the last ~300 KB."""
    import sys
    try:
        if path.exists() and path.stat().st_size > 300_000:
            path.write_text(path.read_text(encoding="utf-8", errors="ignore")[-150_000:], encoding="utf-8")
    except OSError:
        pass
    f = open(path, "a", encoding="utf-8", buffering=1)
    f.write(f"\n===== {datetime.now(ET):%Y-%m-%d %I:%M %p} ET automatic update =====\n")
    sys.stdout = sys.stderr = f


def main():
    now = datetime.now(ET)
    cfg = load_config()
    parser = argparse.ArgumentParser(description="Build the NFL Game Day Board")
    parser.add_argument("--season", type=int, default=now.year if now.month >= 3 else now.year - 1)
    parser.add_argument("--out", default=str(Path(__file__).resolve().parent / "GameDayBoard.html"))
    parser.add_argument("--no-open", action="store_true")
    parser.add_argument("--serve", action="store_true",
                        help="Run the board at http://localhost:8765 with a working Refresh button")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--odds-key", default=os.environ.get("ODDS_API_KEY") or cfg.get("odds_key"),
                        help="The Odds API key (saved key or ODDS_API_KEY is used if omitted)")
    parser.add_argument("--book", default=cfg.get("book", "hardrockbet_fl"),
                        help="Sportsbook key: hardrockbet_fl (default), hardrockbet, hardrockbet_az, hardrockbet_oh")
    parser.add_argument("--odds-days", type=int, default=7, help="Only fetch odds for games within this many days")
    parser.add_argument("--no-odds", action="store_true",
                        help="Rebuild stats, lines, goalies and projections but don't spend Odds API credits (keeps earlier odds)")
    parser.add_argument("--log", action="store_true", help="Append output to board_update.log (used by the automatic update task)")
    parser.add_argument("--odds-today", action="store_true",
                        help="Only buy odds for today's games (ET), NFL and NHL, to save credits")
    parser.add_argument("--shared", action="store_true",
                        help="Build for the shared web link: Refresh reloads the latest published board instead of calling a local server")
    args = parser.parse_args()
    out = Path(args.out).resolve()
    if args.log:
        _log_to_file(Path(__file__).resolve().parent / "board_update.log")

    if args.serve:
        return serve(args.season, out, args.port, not args.no_open)

    print(f"Downloading {args.season} NFL data from nflverse…")
    odds_date = now.date().isoformat() if args.odds_today else None
    data = build_data(args.season, args.odds_key, args.book, args.odds_days, odds_date, fetch_odds=not args.no_odds)
    if args.shared:
        data["shared"] = {"note": "Updates automatically: stats, lines and goalies every 3 hours; Hard Rock odds once a day around 3 PM ET."}
    write_board(data, out)
    print(f"Wrote {out} ({len(data['games'])} games, {len(data['pw'])} player-game rows)")
    if not data["hasPlayerStats"]:
        print("Note: no player stats published for this season yet; positional stats will be blank.")
    if not args.no_open:
        webbrowser.open(out.as_uri())


TEMPLATE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>GameDay Edge Board</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@300;400;500;600;700;800&display=swap" rel="stylesheet">
<style>
/* Game Day Board: navy scoreboard band, turf-green actions, chalk page, amber marks value */
/* folklore-inspired: fog-white page, charcoal bark ink, moss for good, faded rust for bad, wheat marks value */
:root {
  --display: "IM Fell English", "Iowan Old Style", Georgia, serif;
  --body: "EB Garamond", "Iowan Old Style", Georgia, serif;
  --ink: #2f312e; --ink-2: #4a4d48; --paper: #ecece8; --card: #f3f3f6; --soft: #e1e0e5; --line: #d2d1ca;
  --muted: #6d706a; --turf: #56624f; --turf-soft: #e1e5dc; --amber: #43408f; --amber-soft: #e2e0ed;
  --good: #4f6b4a; --bad: #474495; --band: #e4e4df; --band-ink: #2f312e; --band-muted: #6d706a;
  --band-line: rgba(47, 49, 46, 0.22); --band-fill: rgba(255, 255, 255, 0.45); --scheme: light;
  --chip-l: 88%; --chip-s: 20%; --chip-tl: 28%;
  --radius: 4px;
  box-sizing: border-box;
  padding-bottom: env(safe-area-inset-bottom, 0px);
}
@media (prefers-color-scheme: dark) {
  :root { --ink: #e0e0e4; --ink-2: #c9c7c0; --paper: #1d1f1d; --card: #252825; --soft: #2d302c; --line: #3a3e39;
    --muted: #a3a59d; --turf: #9fb096; --turf-soft: #2f372c; --amber: #7e7cc9; --amber-soft: #201f37;
    --good: #a4bd9c; --bad: #908ed1; --band: #242724; --band-ink: #e0e0e4; --band-muted: #a3a59d;
    --band-line: rgba(224, 224, 228, 0.22); --band-fill: rgba(255, 255, 255, 0.06); --scheme: dark;
    --chip-l: 26%; --chip-s: 16%; --chip-tl: 82%; }
}
*, *::before, *::after { box-sizing: inherit; }
html { scroll-padding-top: 140px; }
body { margin: 0; background: var(--paper); color: var(--ink); font: 400 17px/1.5 var(--body); -webkit-font-smoothing: antialiased; font-variant-numeric: lining-nums; }
button, input, select { font: inherit; color: inherit; }
button:focus-visible, input:focus-visible, select:focus-visible, summary:focus-visible { outline: 3px solid var(--amber); outline-offset: 2px; }

/* ---------- masthead (scoreboard band) ---------- */
.masthead { position: sticky; top: 0; z-index: 20; color: var(--band-ink); padding-top: env(safe-area-inset-top, 0px);
  background: linear-gradient(to bottom, var(--band) 0%, color-mix(in srgb, var(--band) 62%, transparent) 60%, var(--band) 100%),
    url("data:image/svg+xml,%3Csvg%20xmlns%3D%22http%3A//www.w3.org/2000/svg%22%20viewBox%3D%220%200%201200%20160%22%20preserveAspectRatio%3D%22xMidYMax%20slice%22%3E%3Crect%20x%3D%22389%22%20y%3D%2223%22%20width%3D%221.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M390%2041%20l-47%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M390%2051%20l-32%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M390%2039%20l-36%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2271%22%20y%3D%2237%22%20width%3D%222.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M72%20116%20l20%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M72%2063%20l-27%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M72%2058%20l-36%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22672%22%20y%3D%22-5%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M674%2048%20l-36%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22743%22%20y%3D%2217%22%20width%3D%222.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M744%2081%20l30%20-21%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M744%2050%20l-40%20-28%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22293%22%20y%3D%2216%22%20width%3D%222.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M294%2068%20l-22%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M294%2065%20l23%20-16%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M294%2072%20l-49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2293%22%20y%3D%2229%22%20width%3D%222.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M95%2095%20l37%20-26%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M95%2076%20l-48%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22569%22%20y%3D%22-7%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M570%2071%20l27%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2048%20l19%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2057%20l-38%20-26%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22592%22%20y%3D%224%22%20width%3D%222.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M593%2056%20l21%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M593%2062%20l46%20-32%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22983%22%20y%3D%224%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M985%2086%20l49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M985%2030%20l-23%20-16%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22790%22%20y%3D%2232%22%20width%3D%221.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M791%2042%20l35%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M791%2089%20l48%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22829%22%20y%3D%2221%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M830%2072%20l31%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22473%22%20y%3D%2210%22%20width%3D%222.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M474%2064%20l-29%20-20%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2263%22%20y%3D%22-2%22%20width%3D%221.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M64%2077%20l-46%20-32%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M64%2077%20l-38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221147%22%20y%3D%2214%22%20width%3D%223.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M1148%20119%20l33%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1148%2054%20l-21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22411%22%20y%3D%2231%22%20width%3D%222.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M412%2058%20l23%20-16%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22652%22%20y%3D%2216%22%20width%3D%221.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M653%2092%20l35%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221090%22%20y%3D%221%22%20width%3D%222.4%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1091%2047%20l-38%20-26%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1091%2097%20l-44%20-31%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1091%20100%20l-24%20-17%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22591%22%20y%3D%2239%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M593%2068%20l32%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M593%20116%20l49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22438%22%20y%3D%221%22%20width%3D%222.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M439%2064%20l-33%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22784%22%20y%3D%22-6%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M785%2095%20l-33%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M785%2025%20l21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221135%22%20y%3D%2213%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M1137%2093%20l-50%20-35%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2233%22%20y%3D%2213%22%20width%3D%223.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M35%20103%20l39%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M35%2057%20l-19%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M35%20101%20l-35%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221120%22%20y%3D%2234%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M1122%2046%20l-27%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22289%22%20y%3D%223%22%20width%3D%223.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M290%2019%20l47%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22795%22%20y%3D%2216%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M797%2038%20l-35%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M797%2028%20l43%20-30%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M797%2083%20l-24%20-16%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22568%22%20y%3D%2218%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M570%2077%20l43%20-30%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2038%20l-26%20-18%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2053%20l-34%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22674%22%20y%3D%2236%22%20width%3D%223.4%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M676%20118%20l-40%20-28%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M676%2079%20l34%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M676%2064%20l48%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221071%22%20y%3D%2212%22%20width%3D%222.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1072%2066%20l-39%20-28%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1072%2064%20l-39%20-28%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22941%22%20y%3D%22-2%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M943%2049%20l46%20-32%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M943%20116%20l-42%20-29%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M943%2018%20l23%20-16%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22801%22%20y%3D%2225%22%20width%3D%222.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M802%2064%20l-29%20-21%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M802%2043%20l19%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22665%22%20y%3D%22-9%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M666%2036%20l-22%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M666%20110%20l-49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M666%2013%20l27%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221087%22%20y%3D%2228%22%20width%3D%222.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M1088%20105%20l31%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1088%2082%20l40%20-28%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1088%2045%20l-44%20-31%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22220%22%20y%3D%223%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M222%2099%20l-37%20-26%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22267%22%20y%3D%22-4%22%20width%3D%222.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M268%2054%20l38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M268%2011%20l-48%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M268%20116%20l20%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22242%22%20y%3D%225%22%20width%3D%222.3%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M243%2062%20l-27%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M243%2099%20l19%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2222%22%20y%3D%2239%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M24%20115%20l-39%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22780%22%20y%3D%2217%22%20width%3D%223.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M782%2056%20l-49%20-35%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M782%2059%20l-31%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M782%2060%20l-45%20-31%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2217%22%20y%3D%2234%22%20width%3D%223.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M19%2050%20l46%20-32%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22805%22%20y%3D%222%22%20width%3D%222.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M806%2032%20l32%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M806%2041%20l49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22656%22%20y%3D%2238%22%20width%3D%222.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M658%2061%20l30%20-21%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M658%2082%20l-26%20-18%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22931%22%20y%3D%2231%22%20width%3D%221.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M932%2044%20l-28%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M932%2091%20l-37%20-26%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M932%2083%20l-39%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22859%22%20y%3D%229%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M861%2035%20l-19%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M861%20103%20l41%20-29%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22975%22%20y%3D%2216%22%20width%3D%221.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M976%20104%20l-21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2250%22%20y%3D%2238%22%20width%3D%223.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M52%2088%20l-38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M52%2097%20l26%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22548%22%20y%3D%2237%22%20width%3D%221.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M549%2095%20l-42%20-29%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22569%22%20y%3D%2232%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M570%2060%20l34%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22459%22%20y%3D%2224%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M461%2088%20l-20%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M461%2047%20l39%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M461%2094%20l-18%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%2273%22%20y%3D%2224%22%20width%3D%223.4%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M75%2076%20l33%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M75%2074%20l-50%20-35%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M75%2081%20l49%20-35%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221124%22%20y%3D%2213%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M1125%20119%20l25%20-17%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1125%20115%20l-20%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22108%22%20y%3D%223%22%20width%3D%225.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M111%20101%20l46%20-32%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M111%2088%20l-34%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M111%20107%20l19%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%224%22%20y%3D%2213%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M6%2063%20l28%20-20%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221008%22%20y%3D%2228%22%20width%3D%222.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M1010%20115%20l-41%20-29%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.6%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221082%22%20y%3D%229%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1084%2026%20l42%20-30%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1084%20105%20l21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1084%20103%20l38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22179%22%20y%3D%2212%22%20width%3D%225.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M182%2099%20l46%20-32%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M182%20102%20l47%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221129%22%20y%3D%2226%22%20width%3D%224.4%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M1131%2071%20l-39%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1131%2060%20l-47%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1131%2082%20l-33%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22412%22%20y%3D%2227%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.18%22/%3E%3Cpath%20d%3D%22M414%2071%20l-28%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M414%2083%20l22%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22772%22%20y%3D%2215%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M773%2046%20l50%20-35%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M773%2068%20l-36%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M773%2048%20l-29%20-20%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22109%22%20y%3D%223%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.15%22/%3E%3Cpath%20d%3D%22M111%2093%20l30%20-21%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22895%22%20y%3D%224%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M897%2043%20l22%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M897%2067%20l-21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221076%22%20y%3D%2222%22%20width%3D%223.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1078%20107%20l-22%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1078%2070%20l49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22588%22%20y%3D%2237%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M589%20109%20l26%20-18%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M589%2055%20l-23%20-16%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M589%20118%20l-48%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22866%22%20y%3D%2228%22%20width%3D%224.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M868%20102%20l-43%20-30%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M868%2057%20l-39%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M868%2063%20l-38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22634%22%20y%3D%2228%22%20width%3D%224.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.12%22/%3E%3Cpath%20d%3D%22M636%2081%20l-30%20-21%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M636%2056%20l-18%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22362%22%20y%3D%2238%22%20width%3D%224.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.15%22/%3E%3Cpath%20d%3D%22M364%2082%20l-36%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%2235%22%20y%3D%2222%22%20width%3D%223.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M37%2076%20l21%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22273%22%20y%3D%229%22%20width%3D%224.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M275%2053%20l30%20-21%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M275%2059%20l-44%20-30%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M275%2094%20l-25%20-17%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221164%22%20y%3D%2231%22%20width%3D%223.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.12%22/%3E%3Cpath%20d%3D%22M1166%2062%20l21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22748%22%20y%3D%2235%22%20width%3D%224.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M751%2049%20l-48%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M751%2049%20l-49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M751%2055%20l-41%20-29%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22221%22%20y%3D%2226%22%20width%3D%224.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M223%20120%20l-29%20-20%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22223%22%20y%3D%2227%22%20width%3D%225.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M226%2097%20l50%20-35%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.4%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M226%2074%20l-18%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.4%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M226%2060%20l31%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.4%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221062%22%20y%3D%2228%22%20width%3D%224.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1064%20105%20l21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1064%2096%20l-30%20-21%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221103%22%20y%3D%228%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M1105%2083%20l-44%20-31%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22920%22%20y%3D%22-8%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M921%2032%20l-47%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22407%22%20y%3D%2238%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.15%22/%3E%3Cpath%20d%3D%22M409%20102%20l48%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M409%2069%20l-19%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22281%22%20y%3D%2238%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.18%22/%3E%3Cpath%20d%3D%22M283%20105%20l44%20-31%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M283%2057%20l24%20-17%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22963%22%20y%3D%2231%22%20width%3D%225.1%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M966%2060%20l33%20-23%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M966%20103%20l-34%20-24%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M966%2072%20l-26%20-18%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%2278%22%20y%3D%2218%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.22%22/%3E%3Cpath%20d%3D%22M80%20109%20l-26%20-19%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M80%2035%20l-31%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%221186%22%20y%3D%22-1%22%20width%3D%229.8%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.20%22/%3E%3Cpath%20d%3D%22M1191%2078%20l-42%20-29%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M1191%20103%20l-43%20-30%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22353%22%20y%3D%223%22%20width%3D%225.7%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.21%22/%3E%3Cpath%20d%3D%22M356%2035%20l-24%20-17%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.4%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M356%2038%20l46%20-32%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.4%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22694%22%20y%3D%2210%22%20width%3D%226.0%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.30%22/%3E%3Cpath%20d%3D%22M697%2073%20l-39%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M697%20119%20l-18%20-13%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M697%20108%20l-45%20-31%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%221097%22%20y%3D%225%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.19%22/%3E%3Cpath%20d%3D%22M1099%2078%20l-48%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22447%22%20y%3D%2212%22%20width%3D%229.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.21%22/%3E%3Cpath%20d%3D%22M451%20115%20l-38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.3%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M451%2092%20l25%20-17%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.3%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M451%2058%20l-19%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.3%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%221200%22%20y%3D%2227%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.29%22/%3E%3Cpath%20d%3D%22M1202%20105%20l40%20-28%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22222%22%20y%3D%220%22%20width%3D%225.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.28%22/%3E%3Cpath%20d%3D%22M225%2063%20l21%20-15%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M225%2054%20l-38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M225%2020%20l-31%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22325%22%20y%3D%2223%22%20width%3D%229.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.23%22/%3E%3Cpath%20d%3D%22M330%2060%20l31%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%2222%22%20y%3D%2230%22%20width%3D%228.6%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.26%22/%3E%3Cpath%20d%3D%22M26%2098%20l-48%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M26%2075%20l-32%20-22%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22984%22%20y%3D%2234%22%20width%3D%226.4%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M988%2054%20l-36%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.6%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22769%22%20y%3D%22-6%22%20width%3D%229.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.25%22/%3E%3Cpath%20d%3D%22M774%2090%20l-23%20-16%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.4%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M774%2037%20l-48%20-33%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.4%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22131%22%20y%3D%2230%22%20width%3D%226.9%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.30%22/%3E%3Cpath%20d%3D%22M134%2064%20l-49%20-34%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.7%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22579%22%20y%3D%2236%22%20width%3D%224.3%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.23%22/%3E%3Cpath%20d%3D%22M581%2092%20l-38%20-27%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M581%20109%20l38%20-26%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M581%2061%20l24%20-17%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22262%22%20y%3D%2216%22%20width%3D%226.4%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.23%22/%3E%3Cpath%20d%3D%22M265%2040%20l-19%20-14%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%221.6%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22675%22%20y%3D%22-8%22%20width%3D%228.5%22%20height%3D%22200%22%20fill%3D%22%232f312e%22%20opacity%3D%220.28%22/%3E%3Cpath%20d%3D%22M679%2048%20l36%20-25%22%20stroke%3D%22%232f312e%22%20stroke-width%3D%222.1%22%20opacity%3D%220.24%22/%3E%3C/svg%3E") center bottom / 1200px 160px repeat-x, var(--band);
  border-bottom: 1px solid var(--line); }
@media (prefers-color-scheme: dark) { .masthead { background: linear-gradient(to bottom, var(--band) 0%, color-mix(in srgb, var(--band) 62%, transparent) 60%, var(--band) 100%),
    url("data:image/svg+xml,%3Csvg%20xmlns%3D%22http%3A//www.w3.org/2000/svg%22%20viewBox%3D%220%200%201200%20160%22%20preserveAspectRatio%3D%22xMidYMax%20slice%22%3E%3Crect%20x%3D%22389%22%20y%3D%2223%22%20width%3D%221.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M390%2041%20l-47%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M390%2051%20l-32%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M390%2039%20l-36%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2271%22%20y%3D%2237%22%20width%3D%222.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M72%20116%20l20%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M72%2063%20l-27%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M72%2058%20l-36%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22672%22%20y%3D%22-5%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M674%2048%20l-36%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22743%22%20y%3D%2217%22%20width%3D%222.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M744%2081%20l30%20-21%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M744%2050%20l-40%20-28%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22293%22%20y%3D%2216%22%20width%3D%222.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M294%2068%20l-22%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M294%2065%20l23%20-16%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M294%2072%20l-49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2293%22%20y%3D%2229%22%20width%3D%222.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M95%2095%20l37%20-26%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M95%2076%20l-48%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22569%22%20y%3D%22-7%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M570%2071%20l27%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2048%20l19%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2057%20l-38%20-26%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22592%22%20y%3D%224%22%20width%3D%222.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M593%2056%20l21%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M593%2062%20l46%20-32%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22983%22%20y%3D%224%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M985%2086%20l49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M985%2030%20l-23%20-16%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22790%22%20y%3D%2232%22%20width%3D%221.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M791%2042%20l35%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M791%2089%20l48%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22829%22%20y%3D%2221%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M830%2072%20l31%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22473%22%20y%3D%2210%22%20width%3D%222.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M474%2064%20l-29%20-20%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2263%22%20y%3D%22-2%22%20width%3D%221.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M64%2077%20l-46%20-32%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M64%2077%20l-38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221147%22%20y%3D%2214%22%20width%3D%223.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M1148%20119%20l33%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1148%2054%20l-21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22411%22%20y%3D%2231%22%20width%3D%222.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M412%2058%20l23%20-16%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22652%22%20y%3D%2216%22%20width%3D%221.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M653%2092%20l35%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221090%22%20y%3D%221%22%20width%3D%222.4%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1091%2047%20l-38%20-26%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1091%2097%20l-44%20-31%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1091%20100%20l-24%20-17%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22591%22%20y%3D%2239%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M593%2068%20l32%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M593%20116%20l49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22438%22%20y%3D%221%22%20width%3D%222.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M439%2064%20l-33%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22784%22%20y%3D%22-6%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M785%2095%20l-33%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M785%2025%20l21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221135%22%20y%3D%2213%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M1137%2093%20l-50%20-35%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2233%22%20y%3D%2213%22%20width%3D%223.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M35%20103%20l39%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M35%2057%20l-19%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M35%20101%20l-35%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221120%22%20y%3D%2234%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M1122%2046%20l-27%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22289%22%20y%3D%223%22%20width%3D%223.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M290%2019%20l47%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22795%22%20y%3D%2216%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M797%2038%20l-35%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M797%2028%20l43%20-30%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M797%2083%20l-24%20-16%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22568%22%20y%3D%2218%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M570%2077%20l43%20-30%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2038%20l-26%20-18%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M570%2053%20l-34%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22674%22%20y%3D%2236%22%20width%3D%223.4%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M676%20118%20l-40%20-28%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M676%2079%20l34%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M676%2064%20l48%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221071%22%20y%3D%2212%22%20width%3D%222.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1072%2066%20l-39%20-28%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1072%2064%20l-39%20-28%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22941%22%20y%3D%22-2%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M943%2049%20l46%20-32%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M943%20116%20l-42%20-29%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M943%2018%20l23%20-16%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22801%22%20y%3D%2225%22%20width%3D%222.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M802%2064%20l-29%20-21%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M802%2043%20l19%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22665%22%20y%3D%22-9%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M666%2036%20l-22%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M666%20110%20l-49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M666%2013%20l27%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%221087%22%20y%3D%2228%22%20width%3D%222.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M1088%20105%20l31%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1088%2082%20l40%20-28%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M1088%2045%20l-44%20-31%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22220%22%20y%3D%223%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M222%2099%20l-37%20-26%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22267%22%20y%3D%22-4%22%20width%3D%222.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.06%22/%3E%3Cpath%20d%3D%22M268%2054%20l38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M268%2011%20l-48%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M268%20116%20l20%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22242%22%20y%3D%225%22%20width%3D%222.3%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.09%22/%3E%3Cpath%20d%3D%22M243%2062%20l-27%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M243%2099%20l19%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2222%22%20y%3D%2239%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M24%20115%20l-39%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22780%22%20y%3D%2217%22%20width%3D%223.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M782%2056%20l-49%20-35%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M782%2059%20l-31%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M782%2060%20l-45%20-31%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2217%22%20y%3D%2234%22%20width%3D%223.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M19%2050%20l46%20-32%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22805%22%20y%3D%222%22%20width%3D%222.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M806%2032%20l32%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M806%2041%20l49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22656%22%20y%3D%2238%22%20width%3D%222.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M658%2061%20l30%20-21%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M658%2082%20l-26%20-18%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22931%22%20y%3D%2231%22%20width%3D%221.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M932%2044%20l-28%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M932%2091%20l-37%20-26%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M932%2083%20l-39%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22859%22%20y%3D%229%22%20width%3D%223.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M861%2035%20l-19%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M861%20103%20l41%20-29%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22975%22%20y%3D%2216%22%20width%3D%221.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M976%20104%20l-21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%2250%22%20y%3D%2238%22%20width%3D%223.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M52%2088%20l-38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Cpath%20d%3D%22M52%2097%20l26%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22548%22%20y%3D%2237%22%20width%3D%221.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.10%22/%3E%3Cpath%20d%3D%22M549%2095%20l-42%20-29%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22569%22%20y%3D%2232%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.07%22/%3E%3Cpath%20d%3D%22M570%2060%20l34%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.08%22/%3E%3Crect%20x%3D%22459%22%20y%3D%2224%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M461%2088%20l-20%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M461%2047%20l39%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M461%2094%20l-18%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%2273%22%20y%3D%2224%22%20width%3D%223.4%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M75%2076%20l33%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M75%2074%20l-50%20-35%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M75%2081%20l49%20-35%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221124%22%20y%3D%2213%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M1125%20119%20l25%20-17%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1125%20115%20l-20%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22108%22%20y%3D%223%22%20width%3D%225.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M111%20101%20l46%20-32%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M111%2088%20l-34%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M111%20107%20l19%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%224%22%20y%3D%2213%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M6%2063%20l28%20-20%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221008%22%20y%3D%2228%22%20width%3D%222.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M1010%20115%20l-41%20-29%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.6%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221082%22%20y%3D%229%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1084%2026%20l42%20-30%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1084%20105%20l21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1084%20103%20l38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22179%22%20y%3D%2212%22%20width%3D%225.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M182%2099%20l46%20-32%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M182%20102%20l47%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221129%22%20y%3D%2226%22%20width%3D%224.4%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M1131%2071%20l-39%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1131%2060%20l-47%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1131%2082%20l-33%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22412%22%20y%3D%2227%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.18%22/%3E%3Cpath%20d%3D%22M414%2071%20l-28%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M414%2083%20l22%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22772%22%20y%3D%2215%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M773%2046%20l50%20-35%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M773%2068%20l-36%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M773%2048%20l-29%20-20%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22109%22%20y%3D%223%22%20width%3D%223.3%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.15%22/%3E%3Cpath%20d%3D%22M111%2093%20l30%20-21%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22895%22%20y%3D%224%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M897%2043%20l22%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M897%2067%20l-21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221076%22%20y%3D%2222%22%20width%3D%223.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1078%20107%20l-22%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1078%2070%20l49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22588%22%20y%3D%2237%22%20width%3D%222.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M589%20109%20l26%20-18%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M589%2055%20l-23%20-16%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M589%20118%20l-48%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22866%22%20y%3D%2228%22%20width%3D%224.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M868%20102%20l-43%20-30%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M868%2057%20l-39%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M868%2063%20l-38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22634%22%20y%3D%2228%22%20width%3D%224.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.12%22/%3E%3Cpath%20d%3D%22M636%2081%20l-30%20-21%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M636%2056%20l-18%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22362%22%20y%3D%2238%22%20width%3D%224.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.15%22/%3E%3Cpath%20d%3D%22M364%2082%20l-36%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%2235%22%20y%3D%2222%22%20width%3D%223.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M37%2076%20l21%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22273%22%20y%3D%229%22%20width%3D%224.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M275%2053%20l30%20-21%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M275%2059%20l-44%20-30%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M275%2094%20l-25%20-17%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221164%22%20y%3D%2231%22%20width%3D%223.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.12%22/%3E%3Cpath%20d%3D%22M1166%2062%20l21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22748%22%20y%3D%2235%22%20width%3D%224.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M751%2049%20l-48%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M751%2049%20l-49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M751%2055%20l-41%20-29%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.2%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22221%22%20y%3D%2226%22%20width%3D%224.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.13%22/%3E%3Cpath%20d%3D%22M223%20120%20l-29%20-20%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22223%22%20y%3D%2227%22%20width%3D%225.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M226%2097%20l50%20-35%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.4%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M226%2074%20l-18%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.4%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M226%2060%20l31%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.4%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221062%22%20y%3D%2228%22%20width%3D%224.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1064%20105%20l21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M1064%2096%20l-30%20-21%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%221103%22%20y%3D%228%22%20width%3D%223.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.17%22/%3E%3Cpath%20d%3D%22M1105%2083%20l-44%20-31%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.8%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22920%22%20y%3D%22-8%22%20width%3D%222.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.11%22/%3E%3Cpath%20d%3D%22M921%2032%20l-47%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.7%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22407%22%20y%3D%2238%22%20width%3D%223.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.15%22/%3E%3Cpath%20d%3D%22M409%20102%20l48%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M409%2069%20l-19%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%220.9%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22281%22%20y%3D%2238%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.18%22/%3E%3Cpath%20d%3D%22M283%20105%20l44%20-31%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M283%2057%20l24%20-17%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.0%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%22963%22%20y%3D%2231%22%20width%3D%225.1%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.16%22/%3E%3Cpath%20d%3D%22M966%2060%20l33%20-23%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M966%20103%20l-34%20-24%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Cpath%20d%3D%22M966%2072%20l-26%20-18%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.3%22%20opacity%3D%220.14%22/%3E%3Crect%20x%3D%2278%22%20y%3D%2218%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.22%22/%3E%3Cpath%20d%3D%22M80%20109%20l-26%20-19%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M80%2035%20l-31%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%221186%22%20y%3D%22-1%22%20width%3D%229.8%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.20%22/%3E%3Cpath%20d%3D%22M1191%2078%20l-42%20-29%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M1191%20103%20l-43%20-30%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22353%22%20y%3D%223%22%20width%3D%225.7%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.21%22/%3E%3Cpath%20d%3D%22M356%2035%20l-24%20-17%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.4%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M356%2038%20l46%20-32%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.4%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22694%22%20y%3D%2210%22%20width%3D%226.0%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.30%22/%3E%3Cpath%20d%3D%22M697%2073%20l-39%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M697%20119%20l-18%20-13%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M697%20108%20l-45%20-31%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%221097%22%20y%3D%225%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.19%22/%3E%3Cpath%20d%3D%22M1099%2078%20l-48%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22447%22%20y%3D%2212%22%20width%3D%229.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.21%22/%3E%3Cpath%20d%3D%22M451%20115%20l-38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.3%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M451%2092%20l25%20-17%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.3%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M451%2058%20l-19%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.3%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%221200%22%20y%3D%2227%22%20width%3D%224.2%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.29%22/%3E%3Cpath%20d%3D%22M1202%20105%20l40%20-28%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22222%22%20y%3D%220%22%20width%3D%225.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.28%22/%3E%3Cpath%20d%3D%22M225%2063%20l21%20-15%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M225%2054%20l-38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M225%2020%20l-31%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22325%22%20y%3D%2223%22%20width%3D%229.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.23%22/%3E%3Cpath%20d%3D%22M330%2060%20l31%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.5%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%2222%22%20y%3D%2230%22%20width%3D%228.6%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.26%22/%3E%3Cpath%20d%3D%22M26%2098%20l-48%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M26%2075%20l-32%20-22%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22984%22%20y%3D%2234%22%20width%3D%226.4%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M988%2054%20l-36%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.6%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22769%22%20y%3D%22-6%22%20width%3D%229.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.25%22/%3E%3Cpath%20d%3D%22M774%2090%20l-23%20-16%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.4%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M774%2037%20l-48%20-33%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.4%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22131%22%20y%3D%2230%22%20width%3D%226.9%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.30%22/%3E%3Cpath%20d%3D%22M134%2064%20l-49%20-34%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.7%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22579%22%20y%3D%2236%22%20width%3D%224.3%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.23%22/%3E%3Cpath%20d%3D%22M581%2092%20l-38%20-27%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M581%20109%20l38%20-26%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Cpath%20d%3D%22M581%2061%20l24%20-17%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.1%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22262%22%20y%3D%2216%22%20width%3D%226.4%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.23%22/%3E%3Cpath%20d%3D%22M265%2040%20l-19%20-14%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%221.6%22%20opacity%3D%220.24%22/%3E%3Crect%20x%3D%22675%22%20y%3D%22-8%22%20width%3D%228.5%22%20height%3D%22200%22%20fill%3D%22%23c9c7c0%22%20opacity%3D%220.28%22/%3E%3Cpath%20d%3D%22M679%2048%20l36%20-25%22%20stroke%3D%22%23c9c7c0%22%20stroke-width%3D%222.1%22%20opacity%3D%220.24%22/%3E%3C/svg%3E") center bottom / 1200px 160px repeat-x, var(--band); } }
body::before { content: ""; position: fixed; inset: 0; pointer-events: none; z-index: 50; opacity: 0.07; background: url("data:image/svg+xml,%3Csvg%20xmlns%3D%22http%3A//www.w3.org/2000/svg%22%20width%3D%22160%22%20height%3D%22160%22%3E%3Cfilter%20id%3D%22n%22%3E%3CfeTurbulence%20type%3D%22fractalNoise%22%20baseFrequency%3D%220.9%22%20numOctaves%3D%222%22%20stitchTiles%3D%22stitch%22/%3E%3CfeColorMatrix%20values%3D%220%200%200%200%200.5%200%200%200%200%200.5%200%200%200%200%200.5%200%200%200%200.55%200%22/%3E%3C/filter%3E%3Crect%20width%3D%22100%25%22%20height%3D%22100%25%22%20filter%3D%22url%28%23n%29%22/%3E%3C/svg%3E"); mix-blend-mode: multiply; }
@media (prefers-color-scheme: dark) { body::before { opacity: 0.05; mix-blend-mode: screen; } }
.mast-in { max-width: 1240px; margin: 0 auto; padding: 14px 20px 10px; display: grid; grid-template-columns: auto 1fr auto; gap: 12px 24px; align-items: center; }
.brand { font: 400 1.5rem/1 var(--display); color: var(--band-muted); white-space: nowrap; }
.brand b { color: var(--band-ink); font-weight: 400; font-style: italic; }
.datenav { display: flex; align-items: center; gap: 10px; min-width: 0; }
.arrow { background: transparent; border: 1.5px solid var(--band-line); color: var(--band-ink); width: 38px; height: 38px;
  border-radius: 50%; font-size: 1.3rem; line-height: 1; cursor: pointer; display: grid; place-items: center; flex: none; }
.arrow:hover { border-color: var(--band-ink); }
.dateblock { min-width: 0; }
.dateline { font: 700 clamp(1.5rem, 3.2vw, 2.1rem)/1 var(--display); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.slate { font-size: 0.85rem; color: var(--band-muted); margin-top: 3px; }
.datetools { display: flex; gap: 6px; align-items: center; margin-left: 6px; }
.datetools input[type=date] { background: var(--band-fill); border: 1.5px solid var(--band-line); color: var(--band-ink);
  border-radius: 8px; padding: 6px 8px; color-scheme: var(--scheme); }
.ghost { white-space: nowrap; background: transparent; border: 1.5px solid var(--band-line); color: var(--band-ink); border-radius: 8px; padding: 7px 11px; cursor: pointer; font-weight: 600; font-size: 0.9rem; }
.ghost:hover { border-color: var(--band-ink); }
.refresh { display: flex; align-items: center; gap: 10px; justify-content: flex-end; position: relative; }
.oddsmsg { font-size: 0.8rem; color: var(--band-muted); max-width: 34ch; text-align: right; line-height: 1.3; }
.oddsmsg.err { color: var(--bad); }
button.primary { background: var(--turf); border: 1.5px solid var(--turf); color: #f3f3f6; letter-spacing: 0.02em; border-radius: var(--radius); padding: 9px 16px; font-weight: 700; cursor: pointer; }
@media (prefers-color-scheme: dark) { button.primary { color: #1d1f1d; } }
button.primary:hover { filter: brightness(1.08); }
button.primary:disabled { opacity: 0.7; cursor: progress; }
.settings summary { list-style: none; cursor: pointer; width: 38px; height: 38px; border-radius: 50%; display: grid; place-items: center;
  border: 1.5px solid var(--band-line); color: var(--band-ink); }
.settings summary::-webkit-details-marker { display: none; }
.settings summary:hover { border-color: var(--band-ink); }
.settings[open] summary { background: var(--band-fill); }
.settings-panel { position: absolute; right: 0; top: calc(100% + 10px); width: min(340px, 90vw); background: var(--card); color: var(--ink);
  border: 1px solid var(--line); border-radius: var(--radius); padding: 16px; display: grid; gap: 12px; box-shadow: 0 12px 32px rgba(10, 20, 35, 0.25); }
.settings-panel label { display: grid; gap: 5px; font-size: 0.85rem; font-weight: 600; color: var(--muted); }
.settings-panel input, .settings-panel select { background: var(--paper); border: 1.5px solid var(--line); border-radius: 8px; padding: 9px 10px; color: var(--ink); }
.settings-panel p { margin: 0; font-size: 0.8rem; color: var(--muted); }

.tabs { max-width: 1240px; margin: 0 auto; padding: 0 20px; display: flex; gap: 4px; overflow-x: auto; scrollbar-width: none; }
.tabs::-webkit-scrollbar { display: none; }
.tabs button { background: none; border: 0; color: var(--band-muted); font: 400 1.2rem/1 var(--display); padding: 10px 14px 12px;
  border-bottom: 3px solid transparent; cursor: pointer; white-space: nowrap; }
.tabs button:hover { color: var(--band-ink); }
.tabs button[aria-pressed=true] { color: var(--band-ink); border-bottom-color: var(--band-ink); font-style: italic; }

/* ---------- page ---------- */
.wrap { max-width: 1240px; margin: 0 auto; padding: 18px 20px 72px; }
.toolbar { display: flex; flex-wrap: wrap; gap: 10px 14px; align-items: center; justify-content: space-between; }
.controls { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; }
.btn, .controls > button:not(.primary), .posf button, .empty button:not(.primary), .error button:not(.primary) {
  background: var(--card); border: 1.5px solid var(--line); border-radius: 8px; padding: 7px 12px; font-weight: 600; font-size: 0.9rem; cursor: pointer; color: var(--ink); }
.controls > button:hover, .posf button:hover { border-color: var(--ink-2); }
.windows, .posf { display: inline-flex; flex-wrap: wrap; gap: 0; background: var(--card); border: 1px solid var(--line); border-radius: var(--radius); padding: 3px; }
.windows button, .posf button { background: none; border: 0; border-radius: 2px; padding: 6px 13px; font-weight: 600; font-size: 0.88rem; cursor: pointer; color: var(--muted); }
.windows button[aria-pressed=true], .posf button[aria-pressed=true] { background: var(--ink); color: var(--paper); }
.howto { margin: 12px 0 0; }
.howto summary { cursor: pointer; color: var(--muted); font-size: 0.88rem; font-weight: 600; width: fit-content; }
.howto summary:hover { color: var(--ink); }
.howto p, .note, .tdctx { font-size: 0.88rem; color: var(--muted); max-width: 88ch; margin: 8px 0 0; }
.alert { margin: 14px 0 0; padding: 10px 14px; border-radius: var(--radius); background: var(--amber-soft); color: var(--ink); font-size: 0.88rem; border: 1px solid color-mix(in srgb, var(--amber) 35%, transparent); }
.alert b { color: var(--amber); }

/* ---------- best edges strip ---------- */
.edges { margin: 18px 0 4px; }
.edges h2 { font: 700 1.35rem/1 var(--display); margin: 0 0 10px; }
.edges .quiet { color: var(--muted); font-size: 0.9rem; margin: 0; }
.ticketrow { display: grid; grid-auto-flow: column; grid-auto-columns: minmax(250px, 1fr); gap: 12px; overflow-x: auto; padding-bottom: 6px; }
.ticket { position: relative; display: grid; grid-template-columns: 48px 1fr; gap: 4px 12px; align-items: center; text-align: left; cursor: pointer;
  background: var(--card); border: 1.5px solid var(--line); border-left: 5px solid var(--amber); border-radius: var(--radius); padding: 12px 14px; color: var(--ink); }
.ticket:hover { border-color: var(--amber); }
.ticket .hs { width: 48px; height: 48px; grid-row: span 2; }
.ticket .who { font: 700 1.15rem/1.1 var(--display); }
.ticket .who small { font: 500 0.8rem var(--body); color: var(--muted); margin-left: 4px; }
.ticket .bet { font-size: 0.9rem; font-weight: 600; }
.ticket .val { grid-column: 1 / -1; display: flex; justify-content: space-between; align-items: baseline; border-top: 1px dashed var(--line); padding-top: 8px; margin-top: 4px; }
.ticket .val b { font: 700 1.5rem/1 var(--display); color: var(--amber); }
.ticket .val span { font-size: 0.82rem; color: var(--muted); }

/* ---------- games view ---------- */
.slot { margin-top: 26px; }
.slot h2, .tdhead h2 { font: 700 1.6rem/1 var(--display); margin: 0 0 12px; display: flex; gap: 10px; align-items: baseline; }
.slot h2 span { font: 500 0.95rem var(--body); color: var(--muted); }
.grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(min(100%, 520px), 1fr)); gap: 16px; }
.game { background: var(--card); border: 1px solid var(--line); border-radius: var(--radius); padding: 16px 18px 12px; min-width: 0; }
.game.final { opacity: 0.92; }
.game:has(details[open]) { grid-column: 1 / -1; }
.meta { font-size: 0.85rem; color: var(--muted); margin-bottom: 10px; font-weight: 600; }
.team { display: grid; grid-template-columns: 34px 1fr auto; gap: 12px; align-items: center; padding: 4px 0; }
.team img, .team .ph { width: 34px; height: 34px; object-fit: contain; }
.team .name { font: 700 1.35rem/1.1 var(--display); }
.team .rec { font-size: 0.85rem; color: var(--muted); margin-left: 8px; }
.team .score { font: 700 1.8rem/1 var(--display); min-width: 2ch; text-align: right; }
.team.lost .score, .team.lost .name { opacity: 0.5; }
.line { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 10px; font-size: 0.85rem; color: var(--muted); }
.line span { background: var(--soft); border-radius: 2px; padding: 2px 10px; }
.line b { color: var(--ink); font-weight: 700; }
.lanes { margin-top: 14px; display: grid; gap: 12px; }
.lane { display: grid; grid-template-columns: 1fr auto 1fr; gap: 8px; align-items: center; }
.side { display: flex; align-items: center; gap: 10px; font-size: 0.92rem; font-weight: 600; }
.side.right { justify-content: flex-end; text-align: right; }
.vs, .ppg, .edge { font-size: 0.78rem; color: var(--muted); font-weight: 500; }
.meter { grid-column: 1 / -1; display: grid; grid-template-columns: 1fr 1fr; height: 6px; background: var(--soft); border-radius: 3px; overflow: hidden; }
.meter i { display: block; height: 100%; }
.meter .l { display: flex; justify-content: flex-end; }
.edge { grid-column: 1 / -1; margin-top: -4px; }
details.props { margin-top: 14px; border-top: 1px solid var(--line); padding-top: 10px; }
details.props summary { cursor: pointer; font: 700 1.15rem var(--display); color: var(--turf); padding: 4px 0; width: fit-content; }
.propgrid h3 { font: 700 1.2rem var(--display); margin: 0 0 6px; }
.mstrip { display: flex; flex-wrap: wrap; gap: 10px 18px; align-items: center; padding: 10px 0; border-bottom: 1px solid var(--line); }
.mlabel { font: 700 1.05rem var(--display); min-width: 13ch; }
.mpos { display: grid; grid-template-columns: auto auto; gap: 2px 6px; align-items: center; }
.mpos .sub { grid-column: 1 / -1; font-size: 0.75rem; color: var(--muted); }

/* ---------- chips and small marks ---------- */
.chip { --h: 60; display: inline-grid; place-items: center; min-width: 38px; height: 28px; padding: 0 7px; border-radius: 6px;
  font: 700 1.1rem/1 var(--display); background: hsl(var(--h) var(--chip-s) var(--chip-l)); color: hsl(var(--h) 60% var(--chip-tl)); }
.chip.na { background: var(--soft); color: var(--muted); }
.pos { display: inline-block; font: 700 0.7rem/1 var(--body); padding: 3px 6px; border-radius: 4px; background: var(--soft); color: var(--muted); margin-right: 6px; vertical-align: 2px; }
.flag { display: inline-block; font-size: 0.72rem; font-weight: 700; color: var(--amber); background: var(--amber-soft); border-radius: 4px; padding: 1px 6px; margin-left: 4px; vertical-align: 1px; }
.flag.adj { color: var(--good); background: var(--turf-soft); }
.up { color: var(--good); } .down { color: var(--bad); } .muted { color: var(--muted); }
.hit { font-weight: 700; color: var(--good); }

/* ---------- tables ---------- */
.tdwrap { margin-top: 24px; }
.tdhead { display: flex; flex-wrap: wrap; gap: 12px 18px; align-items: center; justify-content: space-between; }
.tdhead h2 { margin: 0; }
.tbl { overflow-x: auto; margin: 14px 0 12px; background: var(--card); border: 1px solid var(--line); border-radius: var(--radius); }
table { border-collapse: collapse; width: 100%; font-size: 0.9rem; }
th { position: sticky; top: 0; background: var(--card); text-align: left; font-weight: 600; color: var(--muted); font-size: 0.8rem; padding: 10px 12px; border-bottom: 1.5px solid var(--line); white-space: nowrap; }
td { padding: 12px; border-bottom: 1px solid var(--line); vertical-align: middle; }
tbody tr:last-child td { border-bottom: 0; }
tbody tr:hover td { background: color-mix(in srgb, var(--soft) 70%, transparent); }
td.num { font: 600 1.05rem var(--display); white-space: nowrap; }
td .sub, .sub { display: block; font-size: 0.78rem; color: var(--muted); font-weight: 500; font-family: var(--body); }
tr.value td { background: color-mix(in srgb, var(--amber-soft) 55%, transparent); }
tr.value td:first-child { box-shadow: inset 4px 0 0 var(--amber); }
tr.outrow td { opacity: 0.55; }
.tdtable td { white-space: normal; }
.tdtable td.num { white-space: nowrap; }
.tdtable td:first-child { min-width: 280px; }
.pcell { display: grid; grid-template-columns: 52px 1fr; gap: 12px; align-items: start; }
.pcell > div > :first-child { font-weight: 700; }
.hs { width: 52px; height: 52px; border-radius: 50%; object-fit: cover; object-position: top; background: var(--soft);
  border: 2px solid var(--card); box-shadow: 0 0 0 1px var(--line); display: grid; place-items: center;
  font: 700 1.05rem var(--display); color: var(--muted); }
button.mini { margin-top: 6px; background: transparent; border: 1px solid var(--line); border-radius: 6px; padding: 3px 9px; font-size: 0.74rem; font-weight: 600; cursor: pointer; color: var(--muted); }
button.mini:hover { color: var(--ink); border-color: var(--ink-2); }
.prob { display: grid; grid-template-columns: 3em 1fr; gap: 10px; align-items: center; min-width: 150px; }
.prob b { font: 700 1.35rem var(--display); }
.pbar { height: 8px; background: var(--soft); border-radius: 4px; overflow: hidden; }
.pbar i { display: block; height: 100%; background: var(--turf); border-radius: 4px; }
.oddspair { display: grid; grid-template-columns: 1fr auto 1fr; gap: 10px; align-items: center; min-width: 200px; background: var(--soft); border-radius: 8px; padding: 8px 12px; }
.oside { display: grid; justify-items: start; line-height: 1.15; }
.oside small { font-size: 0.72rem; color: var(--muted); }
.oside b { font: 700 1.35rem var(--display); }
.oside b.muted { font: 600 0.85rem var(--body); }
.ovs { font-weight: 700; color: var(--muted); }
.oin { width: 6.2em; font: 700 1.05rem var(--display); color: var(--ink); background: var(--card); border: 1.5px solid var(--line); border-radius: 6px; padding: 4px 6px; }
.pinputs { display: grid; grid-template-columns: repeat(3, 4.4em); gap: 4px; }
.pinputs .oin { width: 100%; font-size: 0.95rem; padding: 4px; }
.lineb { display: grid; grid-template-columns: auto auto; gap: 0 10px; align-items: baseline; }
.lineb b { font: 700 1.5rem var(--display); grid-row: span 2; }
.lineb span { font-size: 0.85rem; font-weight: 600; }
.ou { display: grid; gap: 3px; font-weight: 600; white-space: nowrap; }
.ou small { color: var(--muted); font-weight: 500; }
b.big { font: 700 1.5rem var(--display); }
.mcell { min-width: 160px; }
.mcell .sub { max-width: 24ch; }
.logc { font: 600 1rem var(--display); white-space: nowrap; }
.edgecell b { font: 700 1.25rem var(--display); }

/* ---------- empty and error ---------- */
.empty, .error { margin-top: 32px; padding: 24px; border: 1.5px dashed var(--line); border-radius: var(--radius); background: var(--card); }
.empty h2, .error h2 { font: 700 1.5rem var(--display); margin: 0 0 6px; }
.empty p, .error p { margin: 0 0 14px; max-width: 64ch; color: var(--muted); }
.loading { margin-top: 36px; color: var(--muted); }

@media (max-width: 860px) {
  .mast-in { grid-template-columns: 1fr auto; }
  .brand { display: none; }
  .datetools input[type=date], #today { display: none; }
}
@media (max-width: 560px) {
  .wrap { padding: 14px 12px 56px; }
  .mast-in { padding: 10px 12px 6px; }
  .tabs { padding: 0 8px; }
  #nextGames { display: none; }
  .oddsmsg { display: none; }
  .side { font-size: 0.85rem; }
}

.dl-short { display: none; }
@media (max-width: 1150px) { .dl-long { display: none; } .dl-short { display: inline; } }
@media (max-width: 560px) {
  .dl-long { display: none; } .dl-short { display: inline; }
  .dateline { font-size: 1.3rem; overflow: visible; text-overflow: clip; }
  .slate { font-size: 0.75rem; white-space: nowrap; }
  .datenav { gap: 6px; } .arrow { width: 30px; height: 30px; font-size: 1.1rem; }
  .refresh { gap: 6px; } button.primary { padding: 8px 12px; } .settings summary { width: 34px; height: 34px; }
}
.hswrap { position: relative; display: inline-block; width: fit-content; height: fit-content; }
.hsbadge { position: absolute; right: -6px; bottom: -4px; width: 26px; height: 26px; object-fit: contain; padding: 2px;
  background: var(--card); border-radius: 50%; box-shadow: 0 0 0 1px var(--line); }
.ticket .hsbadge { width: 22px; height: 22px; right: -5px; bottom: -3px; }
.ticket .hswrap { grid-row: span 2; }
.mup { white-space: nowrap; }
.mlogo { width: 16px; height: 16px; object-fit: contain; vertical-align: -3px; margin-right: 3px; }
/* compact tables: four columns that fit the page, stacked cards on phones */
.tdtable { table-layout: fixed; }
.tdtable col.c-player { width: 34%; } .tdtable col.c-a { width: 18%; } .tdtable col.c-b { width: 24%; } .tdtable col.c-c { width: 24%; }
.tdtable td:first-child { min-width: 0; }
.tdtable td { white-space: normal; overflow-wrap: anywhere; }
.pcell { grid-template-columns: 46px 1fr; gap: 10px; }
.pcell .hs, .pcell .hs-none { width: 46px; height: 46px; }
.pname { font-weight: 700; font-size: 1.05rem; }
.pricepair { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; background: var(--soft); border-radius: var(--radius); padding: 6px 10px; margin-bottom: 6px; }
.pricepair span { display: grid; line-height: 1.15; }
.pricepair small { font-size: 0.72rem; color: var(--muted); }
.pricepair b { font: 600 1.3rem var(--body); font-variant-numeric: lining-nums tabular-nums; }
.pricepair .oin { width: 100%; }
.edgeline { font: 600 1.15rem var(--body); font-variant-numeric: lining-nums tabular-nums; }
.why { display: grid; gap: 4px; font-size: 0.82rem; color: var(--muted); margin-top: 4px; }
.why .chip { min-width: 30px; height: 22px; font-size: 0.95rem; margin-right: 4px; }
.why .logc { font: 500 0.82rem var(--body); white-space: normal; }
.why .logc b { font-weight: 700; }
.ou { margin-top: 6px; white-space: normal; }
.pinputs { grid-template-columns: repeat(3, minmax(0, 1fr)); max-width: 15em; }
@media (max-width: 760px) {
  .tbl { border: 0; background: none; }
  .tdtable, .tdtable tbody, .tdtable tr, .tdtable td { display: block; width: 100%; }
  .tdtable thead, .tdtable colgroup { display: none; }
  .tdtable tr { background: var(--card); border: 1px solid var(--line); border-radius: var(--radius); margin-bottom: 10px; padding: 4px 0; }
  .tdtable td { border: 0; padding: 6px 12px; }
  tr.value td:first-child { box-shadow: none; }
  tr.value { box-shadow: inset 3px 0 0 var(--amber); }
}
/* data figures in Garamond with lining, even-width numerals so columns scan */
td.num, b.big, .chip, .prob b, .oside b, .lineb b, .ticket .val b, .team .score, .oin, .logc, .edgecell b {
  font-family: var(--body); font-variant-numeric: lining-nums tabular-nums; font-weight: 600; }
.dateline, .slot h2, .tdhead h2, .edges h2, .team .name, .ticket .who, details.props summary, .mlabel, .empty h2, .error h2, .propgrid h3 { font-weight: 400; }
.dateline { font-size: clamp(1.7rem, 3.4vw, 2.4rem); }
.slot h2, .tdhead h2 { font-size: 1.9rem; }
.edges h2 { font-size: 1.6rem; font-style: italic; }
.team .name { font-size: 1.45rem; }
.ticket { border-left: 3px solid var(--amber); box-shadow: none; }
.ticket .who { font-size: 1.25rem; }
.ticket .val b { font-size: 1.45rem; }
.hs { filter: grayscale(0.35) contrast(0.95); }
.team img { filter: grayscale(0.5); opacity: 0.9; }
.pbar i { background: var(--ink-2); }
.pos { font: 600 0.72rem/1 var(--body); letter-spacing: 0.04em; }
th { font: 500 0.88rem var(--body); font-style: italic; }
.howto summary { font-style: italic; }
.game, .tbl, .ticket, .empty, .error, .settings-panel { border-radius: var(--radius); }
.game { border-color: var(--line); }
tr.value td:first-child { box-shadow: inset 3px 0 0 var(--amber); }
/* ================= Liquid glass theme (overrides everything above) ================= */
:root {
  --display: "Poppins", "Segoe UI Variable", "Segoe UI", system-ui, sans-serif;
  --body: "Poppins", "Segoe UI Variable", "Segoe UI", system-ui, sans-serif;
  --bg: #080812; --ink: #eceaf4; --ink-2: #d2d0dd; --muted: rgba(236, 234, 244, 0.58);
  --paper: #080812; --card: rgba(255, 255, 255, 0.055); --soft: rgba(255, 255, 255, 0.07); --line: rgba(255, 255, 255, 0.10);
  --turf: #9842fa; --turf-soft: rgba(94, 230, 168, 0.14); --amber: #a65bfb; --amber-soft: rgba(152, 66, 250, 0.14);
  --good: #6ee7b0; --bad: #ff8f7e; --band: transparent; --band-ink: var(--ink); --band-muted: var(--muted);
  --band-line: rgba(255, 255, 255, 0.14); --band-fill: rgba(255, 255, 255, 0.07); --scheme: dark;
  --chip-l: 24%; --chip-s: 38%; --chip-tl: 80%;
  --radius: 22px; --r-sm: 14px;
  --orange: linear-gradient(135deg, #a962fb 0%, #9034fa 55%, #791be4 100%);
  --glass: linear-gradient(145deg, rgba(255, 255, 255, 0.11) 0%, rgba(255, 255, 255, 0.035) 45%, rgba(255, 255, 255, 0.06) 100%);
  --glass-strong: linear-gradient(145deg, rgba(255, 255, 255, 0.16) 0%, rgba(255, 255, 255, 0.06) 100%);
  --glass-edge: inset 0 1px 0 rgba(255, 255, 255, 0.22), inset 0 -1px 0 rgba(0, 0, 0, 0.25), inset 1px 0 0 rgba(255, 255, 255, 0.06);
  --glass-shadow: 0 24px 60px -18px rgba(0, 0, 0, 0.65), 0 2px 8px rgba(0, 0, 0, 0.25);
  --blur: blur(26px) saturate(165%);
  color-scheme: dark;
}
html { background: var(--bg); scroll-padding-top: 170px; }
body { background: transparent; color: var(--ink); font: 400 15px/1.5 var(--body); letter-spacing: -0.005em; font-variant-numeric: tabular-nums; min-height: 100vh; }
/* ambient light the glass refracts: warm lamps in a dark room */
body::after { content: ""; position: fixed; inset: -10%; z-index: -1; pointer-events: none;
  background:
    radial-gradient(38% 42% at 12% 8%, rgba(151, 65, 250, 0.38), transparent 70%),
    radial-gradient(30% 36% at 88% 18%, rgba(174, 106, 251, 0.22), transparent 70%),
    radial-gradient(45% 45% at 70% 92%, rgba(116, 35, 209, 0.30), transparent 70%),
    radial-gradient(35% 40% at 22% 85%, rgba(46, 44, 106, 0.35), transparent 70%),
    linear-gradient(180deg, #0b0b1a 0%, #080812 55%, #06060d 100%);
  filter: blur(10px); }
body::before { opacity: 0.035; mix-blend-mode: overlay; }
::selection { background: rgba(152, 66, 250, 0.45); }
button:focus-visible, input:focus-visible, select:focus-visible, summary:focus-visible { outline: 2px solid #ac7dfc; outline-offset: 2px; }

/* glass surfaces */
.masthead, .game, .tbl, .ticket, .empty, .error, .windows, .posf, .settings-panel, .glass, .sport, .views {
  background: var(--glass); border: 1px solid rgba(255, 255, 255, 0.12);
  -webkit-backdrop-filter: var(--blur); backdrop-filter: var(--blur);
  box-shadow: var(--glass-edge), var(--glass-shadow); }

/* ---------- masthead: floating glass bar ---------- */
.masthead { position: sticky; top: 10px; margin: 10px auto 0; max-width: 1280px; width: calc(100% - 24px);
  border-radius: 28px; border-bottom: 1px solid rgba(255, 255, 255, 0.12); padding-bottom: 10px; z-index: 30; }
.mast-in { padding: 12px 18px 8px; max-width: none; }
.brand { font: 700 1.05rem/1 var(--display); color: var(--muted); letter-spacing: -0.01em; display: flex; align-items: center; gap: 10px; }
.brand::before { content: ""; width: 30px; height: 30px; border-radius: 10px; background: var(--orange);
  box-shadow: 0 6px 18px rgba(144, 52, 250, 0.45), inset 0 1px 0 rgba(255, 255, 255, 0.5); }
.brand b { font-style: normal; font-weight: 800; color: var(--ink); }
.dateline { font: 700 clamp(1.3rem, 2.6vw, 1.85rem)/1.1 var(--display); letter-spacing: -0.02em; }
.slate { color: var(--muted); font-size: 0.82rem; }
.arrow, .settings summary { background: rgba(255, 255, 255, 0.07); border: 1px solid rgba(255, 255, 255, 0.12); box-shadow: var(--glass-edge);
  width: 38px; height: 38px; border-radius: 50%; transition: background .2s, transform .2s; }
.arrow:hover, .settings summary:hover { background: rgba(255, 255, 255, 0.14); border-color: rgba(255, 255, 255, 0.2); transform: translateY(-1px); }
.ghost, .datetools input[type=date] { background: rgba(255, 255, 255, 0.07); border: 1px solid rgba(255, 255, 255, 0.12); border-radius: 999px;
  padding: 8px 14px; color: var(--ink); box-shadow: var(--glass-edge); font-weight: 600; font-size: 0.85rem; }
.datetools input[type=date] { padding: 7px 12px; }
.ghost:hover { background: rgba(255, 255, 255, 0.14); border-color: rgba(255, 255, 255, 0.2); }
button.primary { background: var(--orange); border: 1px solid rgba(189, 153, 252, 0.55); color: #0a0917; border-radius: 999px; padding: 9px 20px;
  font-weight: 800; letter-spacing: 0; box-shadow: 0 10px 28px -6px rgba(144, 52, 250, 0.65), inset 0 1px 0 rgba(255, 255, 255, 0.55); transition: transform .2s, box-shadow .2s; }
button.primary:hover { filter: none; transform: translateY(-1px); box-shadow: 0 14px 34px -6px rgba(144, 52, 250, 0.8), inset 0 1px 0 rgba(255, 255, 255, 0.6); }
.oddsmsg { color: var(--muted); }
.settings-panel { background: linear-gradient(160deg, rgba(29, 28, 58, 0.94), rgba(15, 15, 30, 0.96)); border-radius: var(--radius); color: var(--ink); }
.settings-panel input, .settings-panel select { background: rgba(0, 0, 0, 0.3); border: 1px solid rgba(255, 255, 255, 0.14); border-radius: 12px; color: var(--ink); }
.settings-panel label, .settings-panel p { color: var(--muted); }

/* nav row: sport switch + view tabs as glass capsules */
.navrow { display: flex; gap: 10px; align-items: center; padding: 2px 14px 0; overflow-x: auto; scrollbar-width: none; }
.navrow::-webkit-scrollbar { display: none; }
.sport, .views { display: inline-flex; gap: 2px; padding: 4px; border-radius: 999px; flex: none; box-shadow: var(--glass-edge); }
.views { max-width: none; margin: 0; overflow: visible; }
.sport button, .tabs button { background: none; border: 0; border-radius: 999px; padding: 8px 16px; font: 600 0.88rem/1 var(--body);
  color: var(--muted); cursor: pointer; white-space: nowrap; transition: background .2s, color .2s; font-style: normal; border-bottom: 0; }
.sport button:hover, .tabs button:hover { color: var(--ink); background: rgba(255, 255, 255, 0.06); }
.sport button[aria-pressed=true] { background: var(--orange); color: #0a0917; font-weight: 800;
  box-shadow: 0 6px 18px -4px rgba(144, 52, 250, 0.7), inset 0 1px 0 rgba(255, 255, 255, 0.5); }
.tabs button[aria-pressed=true] { background: rgba(255, 255, 255, 0.15); color: var(--ink); font-style: normal;
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.25), 0 4px 14px rgba(0, 0, 0, 0.25); }
.tabs button[aria-pressed=true]::before { content: ""; display: inline-block; width: 6px; height: 6px; border-radius: 50%; background: #a65bfb;
  box-shadow: 0 0 8px #9842fa; margin-right: 8px; vertical-align: 2px; }
body[data-sport=nfl] .nhl-only, body[data-sport=nhl] .nfl-only { display: none !important; }

/* ---------- page ---------- */
.wrap { max-width: 1280px; padding: 22px 24px 80px; }
.windows, .posf { border-radius: 999px; padding: 4px; gap: 2px; }
.windows button, .posf button { border-radius: 999px; padding: 7px 14px; color: var(--muted); font-weight: 600; font-size: 0.84rem; }
.windows button:hover, .posf button:hover { color: var(--ink); }
.windows button[aria-pressed=true], .posf button[aria-pressed=true] { background: rgba(152, 66, 250, 0.2); color: #c09dfc;
  box-shadow: inset 0 0 0 1px rgba(166, 91, 251, 0.45), inset 0 1px 0 rgba(255, 255, 255, 0.15); }
.btn, .controls > button:not(.primary), .posf button, .empty button:not(.primary), .error button:not(.primary) { border-radius: 999px; }
.btn, .controls > button:not(.primary), .empty button:not(.primary), .error button:not(.primary) {
  background: rgba(255, 255, 255, 0.07); border: 1px solid rgba(255, 255, 255, 0.12); color: var(--ink); padding: 8px 15px; box-shadow: var(--glass-edge); font-size: 0.84rem; }
.controls > button:hover { background: rgba(255, 255, 255, 0.13); border-color: rgba(255, 255, 255, 0.2); }
.howto summary { font-style: normal; color: var(--muted); }
.alert { background: rgba(152, 66, 250, 0.12); border: 1px solid rgba(166, 91, 251, 0.3); border-radius: var(--r-sm); color: var(--ink); }
.alert b { color: #ac7dfc; }

.slot h2, .tdhead h2, .edges h2 { font: 700 1.45rem/1.1 var(--display); letter-spacing: -0.02em; font-style: normal; }
.slot h2 span { font: 500 0.85rem var(--body); color: var(--muted); }
.edges h2::after { content: ""; display: inline-block; width: 8px; height: 8px; border-radius: 50%; background: var(--good); box-shadow: 0 0 10px var(--good); margin-left: 10px; vertical-align: 4px; }

/* game cards */
.grid { gap: 18px; }
.game { border-radius: var(--radius); padding: 18px 20px 14px; transition: transform .25s, box-shadow .25s; }
.game:hover { transform: translateY(-2px); box-shadow: var(--glass-edge), 0 30px 70px -18px rgba(0, 0, 0, 0.75), 0 0 0 1px rgba(166, 91, 251, 0.12); }
.meta { color: var(--muted); font-weight: 600; font-size: 0.8rem; }
.team .name { font: 700 1.2rem/1.15 var(--display); letter-spacing: -0.015em; }
.team .score { font: 800 1.7rem/1 var(--display); }
.team img { filter: none; opacity: 1; }
.line span { background: rgba(255, 255, 255, 0.07); border: 1px solid rgba(255, 255, 255, 0.08); border-radius: 999px; padding: 3px 11px; }
.meter { background: rgba(255, 255, 255, 0.08); height: 6px; }
details.props { border-top: 1px solid rgba(255, 255, 255, 0.08); }
details.props summary { font: 700 0.95rem var(--display); color: #ac7dfc; }
.propgrid h3, .mlabel { font: 700 1rem var(--display); }
.mstrip { border-bottom-color: rgba(255, 255, 255, 0.08); }

/* chips / marks */
.chip { border-radius: 10px; font: 700 0.95rem/1 var(--body); box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.12); }
.pos { background: rgba(255, 255, 255, 0.09); color: var(--ink-2); border-radius: 999px; padding: 3px 8px; font: 700 0.68rem/1 var(--body); }
.flag { background: rgba(152, 66, 250, 0.16); color: #ac7dfc; border-radius: 999px; padding: 2px 8px; }
.flag.adj { background: rgba(110, 231, 176, 0.14); color: var(--good); }
.up, .hit { color: var(--good); } .down { color: var(--bad); }

/* best-edge tickets */
.ticketrow { gap: 14px; padding: 4px 2px 10px; }
.ticket { border-radius: var(--radius); border-left: 1px solid rgba(255, 255, 255, 0.12); padding: 14px 16px; overflow: hidden; transition: transform .25s; }
.ticket::before { content: ""; position: absolute; inset: 0 0 auto 0; height: 3px; background: var(--orange); opacity: 0.9; }
.ticket::after { content: ""; position: absolute; right: -40px; top: -40px; width: 120px; height: 120px; border-radius: 50%;
  background: radial-gradient(circle, rgba(152, 66, 250, 0.35), transparent 70%); pointer-events: none; }
.ticket:hover { transform: translateY(-2px); border-color: rgba(166, 91, 251, 0.35); }
.ticket .who { font: 700 1.05rem/1.15 var(--display); }
.ticket .val { border-top: 1px solid rgba(255, 255, 255, 0.08); }
.ticket .val b { font: 800 1.4rem/1 var(--display); color: var(--good); text-shadow: 0 0 18px rgba(110, 231, 176, 0.35); }

/* tables inside glass */
.tbl { border-radius: var(--radius); }
table { font-size: 0.88rem; }
th { background: rgba(13, 13, 26, 0.82); -webkit-backdrop-filter: blur(12px); backdrop-filter: blur(12px); color: var(--muted);
  font: 600 0.72rem var(--body); font-style: normal; text-transform: uppercase; letter-spacing: 0.07em; border-bottom: 1px solid rgba(255, 255, 255, 0.08); }
td { border-bottom: 1px solid rgba(255, 255, 255, 0.06); }
tbody tr { transition: background .15s; }
tbody tr:hover td { background: rgba(255, 255, 255, 0.04); }
tr.value td { background: linear-gradient(90deg, rgba(152, 66, 250, 0.14), rgba(152, 66, 250, 0.02) 60%); }
tr.value td:first-child { box-shadow: inset 3px 0 0 #9842fa; }
.pname { font-weight: 700; font-size: 1rem; letter-spacing: -0.01em; }
.hs { filter: none; background: linear-gradient(145deg, rgba(255, 255, 255, 0.16), rgba(255, 255, 255, 0.04)); border: 1px solid rgba(255, 255, 255, 0.18);
  box-shadow: 0 6px 16px rgba(0, 0, 0, 0.35); font: 700 0.95rem var(--body); color: var(--ink-2); }
.hsbadge { background: rgba(15, 15, 30, 0.9); box-shadow: 0 0 0 1px rgba(255, 255, 255, 0.16); }
.pbar { background: rgba(255, 255, 255, 0.08); height: 7px; border-radius: 999px; }
.pbar i { background: var(--orange); border-radius: 999px; box-shadow: 0 0 12px rgba(144, 52, 250, 0.55); }
.prob b, td.num, b.big, .edgeline, .edgecell b, .lineb b, .oside b, .pricepair b { font-family: var(--body); font-weight: 700; letter-spacing: -0.02em; }
.pricepair, .oddspair { background: rgba(255, 255, 255, 0.06); border: 1px solid rgba(255, 255, 255, 0.08); border-radius: var(--r-sm); box-shadow: var(--glass-edge); }
.oin { background: rgba(0, 0, 0, 0.28); border: 1px solid rgba(255, 255, 255, 0.14); border-radius: 10px; color: var(--ink); font: 700 0.95rem var(--body); }
.oin:focus { border-color: #a65bfb; box-shadow: 0 0 0 3px rgba(152, 66, 250, 0.25); outline: none; }
button.mini { border-radius: 999px; border: 1px solid rgba(255, 255, 255, 0.14); background: rgba(255, 255, 255, 0.05); color: var(--muted); }
button.mini:hover { background: rgba(255, 255, 255, 0.12); color: var(--ink); border-color: rgba(255, 255, 255, 0.22); }
.why .logc { font-family: var(--body); }
.empty, .error { border-radius: var(--radius); border-style: solid; }
.empty h2, .error h2 { font: 700 1.3rem var(--display); }

@media (max-width: 760px) {
  .tbl { background: none; border: 0; box-shadow: none; -webkit-backdrop-filter: none; backdrop-filter: none; }
  .tdtable tr { background: var(--glass); border: 1px solid rgba(255, 255, 255, 0.12); border-radius: var(--radius);
    -webkit-backdrop-filter: var(--blur); backdrop-filter: var(--blur); box-shadow: var(--glass-edge), var(--glass-shadow); }
  tr.value { box-shadow: inset 3px 0 0 #9842fa, var(--glass-edge); }
  tr.value td, tr.value td:first-child { background: none; box-shadow: none; }
}
@media (max-width: 860px) { .brand { display: none; } }
@media (max-width: 560px) {
  .masthead { width: calc(100% - 16px); top: 6px; margin-top: 6px; border-radius: 22px; }
  .wrap { padding: 16px 12px 60px; }
  .navrow { padding: 2px 8px 0; }
  .sport button, .tabs button { padding: 7px 12px; font-size: 0.82rem; }
}
@media (max-width: 560px) {
  .dateblock { overflow: hidden; }
  .slate { overflow: hidden; text-overflow: ellipsis; max-width: 42vw; }
  .nhlbar .lbl { display: none; }
  .refresh button.primary { padding: 7px 12px; font-size: 0.85rem; }
  .dateline { font-size: 1.12rem !important; }
  .mast-in { gap: 8px; padding: 10px 10px 6px; }
}

/* ---------- main sport tabs: NHL | NFL ---------- */
.sportbar { display: flex; justify-content: center; padding: 12px 14px 0; }
.sportbar .sport { padding: 5px; gap: 4px; background: rgba(0, 0, 0, 0.22); }
.sportbar .sport button { padding: 11px 34px; font: 800 1.02rem/1 var(--display); letter-spacing: 0.04em; display: inline-flex; align-items: center; gap: 9px; }
.sportbar .sdot { width: 7px; height: 7px; border-radius: 50%; background: rgba(255, 255, 255, 0.25); transition: background .2s, box-shadow .2s; }
.sportbar .sport button[aria-pressed=true] .sdot { background: #0a0917; box-shadow: 0 0 0 3px rgba(255, 255, 255, 0.35); }
.masthead { top: 8px; }
.mast-in { padding-top: 8px; }
html { scroll-padding-top: 210px; }
@media (max-width: 560px) { .sportbar { padding-top: 8px; } .sportbar .sport { width: 100%; } .sportbar .sport button { flex: 1; justify-content: center; padding: 10px 0; } }
.lupill { background: rgba(152, 66, 250, 0.14) !important; border-color: rgba(166, 91, 251, 0.35) !important; color: #c09dfc !important; font-weight: 700; }
.statpills small { color: var(--muted); font-size: 0.7rem; }
/* status message sits under the Refresh button instead of squeezing the date */
.refresh .oddsmsg { position: absolute; right: 4px; top: calc(100% + 8px); max-width: min(62ch, 70vw); text-align: right; font-size: 0.78rem; pointer-events: none; }
.dateblock { min-width: 14ch; }
.slate { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
@media (max-width: 860px) { .refresh .oddsmsg { position: static; display: none; } }

/* ================= v2 look: stronger liquid glass, lamp-lit room ambience ================= */
:root { --radius: 28px; --r-sm: 18px; --blur: blur(34px) saturate(180%);
  --glass: linear-gradient(150deg, rgba(233, 221, 254, 0.16) 0%, rgba(255, 255, 255, 0.05) 42%, rgba(195, 162, 253, 0.08) 100%);
  --glass-edge: inset 0 1px 0 rgba(255, 255, 255, 0.30), inset 0 -1px 0 rgba(0, 0, 0, 0.30), inset 1px 0 0 rgba(255, 255, 255, 0.08), inset -1px 0 0 rgba(255, 255, 255, 0.04);
  --glass-shadow: 0 30px 80px -24px rgba(0, 0, 0, 0.75), 0 2px 10px rgba(0, 0, 0, 0.3); }
body { font-weight: 400; letter-spacing: 0; }
body::after { inset: -15%; filter: blur(18px);
  background:
    radial-gradient(14% 18% at 18% 10%, rgba(170, 123, 252, 0.85), transparent 70%),
    radial-gradient(30% 34% at 18% 12%, rgba(151, 65, 250, 0.45), transparent 72%),
    radial-gradient(10% 14% at 84% 16%, rgba(189, 153, 252, 0.7), transparent 70%),
    radial-gradient(26% 30% at 84% 18%, rgba(157, 75, 250, 0.32), transparent 72%),
    radial-gradient(40% 30% at 55% 105%, rgba(124, 35, 225, 0.45), transparent 70%),
    radial-gradient(22% 26% at 6% 70%, rgba(52, 49, 121, 0.55), transparent 72%),
    radial-gradient(28% 30% at 96% 72%, rgba(45, 43, 105, 0.5), transparent 72%),
    radial-gradient(3% 4% at 40% 30%, rgba(170, 123, 252, 0.35), transparent 70%),
    radial-gradient(2.5% 3.5% at 66% 42%, rgba(170, 123, 252, 0.3), transparent 70%),
    radial-gradient(2% 3% at 30% 62%, rgba(178, 114, 251, 0.25), transparent 70%),
    linear-gradient(180deg, #0f0e23 0%, #090916 45%, #06060e 100%); }
html::before { content: ""; position: fixed; inset: 0; z-index: -1; pointer-events: none;
  background: radial-gradient(120% 90% at 50% 40%, transparent 55%, rgba(0, 0, 0, 0.55) 100%); }
.masthead { border-radius: 32px; background: linear-gradient(150deg, rgba(38, 36, 88, 0.80) 0%, rgba(18, 17, 38, 0.86) 45%, rgba(24, 23, 57, 0.84) 100%); }
.slot h2, .tdhead h2, .edges h2 { font-weight: 600; letter-spacing: -0.01em; }
.dateline { font-weight: 600; letter-spacing: -0.02em; }
.stat { border-radius: 24px; padding: 18px 22px; }
.stat b { font-weight: 600; font-size: 1.9rem; }
.gpill { border-radius: 20px; padding: 10px 16px; }
.game { border-radius: 28px; }

/* ---------- NHL player cards ---------- */
.pgrid { display: grid; grid-template-columns: repeat(auto-fill, minmax(min(100%, 330px), 1fr)); gap: 18px; margin: 18px 0 12px; }
.pcard { position: relative; display: grid; gap: 14px; padding: 18px 18px 14px; border-radius: 28px; overflow: hidden;
  background: var(--glass); border: 1px solid rgba(255, 255, 255, 0.13); -webkit-backdrop-filter: var(--blur); backdrop-filter: var(--blur);
  box-shadow: var(--glass-edge), var(--glass-shadow); transition: transform .25s, box-shadow .25s, border-color .25s; }
.pcard::before { content: ""; position: absolute; inset: -40% -30% auto auto; width: 70%; height: 80%; border-radius: 50%; pointer-events: none;
  background: radial-gradient(circle, rgba(173, 104, 251, 0.16), transparent 65%); }
.pcard:hover { transform: translateY(-3px); border-color: rgba(183, 143, 252, 0.28); box-shadow: var(--glass-edge), 0 36px 90px -24px rgba(0, 0, 0, 0.85); }
.pcard.value { border-color: rgba(110, 231, 176, 0.45); box-shadow: var(--glass-edge), 0 0 0 1px rgba(110, 231, 176, 0.15), 0 30px 80px -24px rgba(0, 0, 0, 0.75), 0 0 40px -10px rgba(110, 231, 176, 0.35); }
.pcard.outcard { opacity: 0.55; }
.pc-top { display: grid; grid-template-columns: 64px 1fr auto; gap: 14px; align-items: center; position: relative; }
.pc-photo { position: relative; width: 64px; height: 64px; border-radius: 50%;
  background: radial-gradient(circle at 50% 35%, rgba(189, 153, 252, 0.35), rgba(255, 255, 255, 0.05) 70%);
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.35), 0 8px 20px rgba(0, 0, 0, 0.4); border: 1px solid rgba(255, 255, 255, 0.18); }
.pc-photo img { width: 100%; height: 100%; border-radius: 50%; object-fit: cover; object-position: top; }
.pc-photo .ini { display: grid; place-items: center; width: 100%; height: 100%; font-weight: 600; font-size: 1.1rem; color: var(--ink-2); }
.pc-logo { position: absolute; right: -6px; bottom: -4px; width: 26px; height: 26px; padding: 3px; border-radius: 50%;
  background: rgba(11, 11, 26, 0.9); box-shadow: 0 0 0 1px rgba(255, 255, 255, 0.18); }
.pc-who { min-width: 0; }
.pc-name { font-weight: 600; font-size: 1.08rem; letter-spacing: -0.01em; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.pc-meta { font-size: 0.78rem; color: var(--muted); margin-top: 1px; }
.pc-meta .pos { margin-right: 6px; }
.pc-chips { display: flex; flex-wrap: wrap; gap: 5px; margin-top: 7px; }
.pc-chips span { font-size: 0.7rem; padding: 2px 9px; border-radius: 999px; background: rgba(255, 255, 255, 0.07); border: 1px solid rgba(255, 255, 255, 0.1); color: var(--ink-2); }
.ring { position: relative; width: 72px; height: 72px; }
.ring svg { width: 100%; height: 100%; transform: rotate(-90deg); }
.ring-bg { fill: rgba(0, 0, 0, 0.18); stroke: rgba(255, 255, 255, 0.10); stroke-width: 7; }
.ring-fg { fill: none; stroke: url(#rg); stroke-width: 7; stroke-linecap: round; filter: drop-shadow(0 0 5px rgba(146, 55, 250, 0.55)); }
.ring b { position: absolute; inset: 0; display: flex; align-items: center; justify-content: center; font-weight: 600; font-size: 1.15rem; letter-spacing: -0.02em; }
.ring b small { font-size: 0.62rem; font-weight: 500; color: var(--muted); margin-left: 1px; align-self: flex-start; margin-top: 25px; }
.pc-market { display: grid; grid-template-columns: 1.1fr 1fr 1fr; gap: 8px; }
.pc-market.manual { grid-template-columns: auto 1fr; align-items: center; }
.pc-line, .pc-price { border-radius: 16px; padding: 8px 12px; background: rgba(0, 0, 0, 0.2); border: 1px solid rgba(255, 255, 255, 0.08);
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.06); display: grid; gap: 1px; }
.pc-line { background: linear-gradient(145deg, rgba(152, 66, 250, 0.22), rgba(152, 66, 250, 0.06)); border-color: rgba(166, 91, 251, 0.35); }
.pc-line small, .pc-price small { font-size: 0.66rem; color: var(--muted); text-transform: uppercase; letter-spacing: 0.06em; }
.pc-line b { font-size: 1.35rem; font-weight: 600; color: #c8aafd; }
.pc-price b { font-size: 1.2rem; font-weight: 600; }
.pc-price.good { border-color: rgba(110, 231, 176, 0.45); background: rgba(110, 231, 176, 0.08); }
.pc-price.good b { color: var(--good); }
.pc-manual { display: flex; align-items: center; justify-content: space-between; gap: 10px; padding: 8px 8px 8px 14px; border-radius: 16px;
  background: rgba(0, 0, 0, 0.18); border: 1px dashed rgba(255, 255, 255, 0.14); font-size: 0.78rem; color: var(--muted); }
.pc-alts { font-size: 0.72rem; color: var(--muted); margin-top: -6px; }
.pc-edge { display: flex; align-items: baseline; gap: 10px; padding: 10px 14px; border-radius: 16px; background: rgba(255, 255, 255, 0.05); border: 1px solid rgba(255, 255, 255, 0.08); }
.pc-edge span { font-size: 0.72rem; text-transform: uppercase; letter-spacing: 0.07em; color: var(--muted); }
.pc-edge b { font-size: 1.1rem; font-weight: 600; }
.pc-edge em { font-style: normal; margin-left: auto; font-size: 0.8rem; color: var(--muted); }
.pc-edge.pos { background: linear-gradient(90deg, rgba(110, 231, 176, 0.16), rgba(110, 231, 176, 0.03)); border-color: rgba(110, 231, 176, 0.35); }
.pc-edge.pos b, .pc-edge.pos em { color: var(--good); }
.pc-edge.neg b { color: var(--bad); }
.pc-edge.none b { color: var(--muted); font-weight: 500; font-size: 0.9rem; }
.pc-edge.win { background: rgba(110, 231, 176, 0.12); } .pc-edge.win b { color: var(--good); }
.pc-edge.loss b { color: var(--bad); }
.pc-foot { display: flex; flex-wrap: wrap; align-items: center; gap: 6px 14px; font-size: 0.74rem; color: var(--muted); padding-top: 2px; border-top: 1px solid rgba(255, 255, 255, 0.07); padding-top: 10px; }
.pc-foot b { color: var(--ink-2); font-weight: 600; }
.pc-foot i { font-style: normal; color: #ac7dfc; font-size: 0.65rem; }
.pc-foot .mini { margin: 0 0 0 auto; }

/* ---------- NFL tables as glass cards too ---------- */
@media (min-width: 761px) {
  body[data-sport=nfl] .tbl { background: none; border: 0; box-shadow: none; -webkit-backdrop-filter: none; backdrop-filter: none; overflow: visible; }
  body[data-sport=nfl] .tdtable, body[data-sport=nfl] .tdtable tbody { display: block; width: 100%; }
  body[data-sport=nfl] .tdtable thead, body[data-sport=nfl] .tdtable colgroup { display: none; }
  body[data-sport=nfl] .tdtable tbody { display: grid; grid-template-columns: repeat(auto-fill, minmax(360px, 1fr)); gap: 18px; }
  body[data-sport=nfl] .tdtable tr { display: grid; gap: 10px; padding: 16px 18px; border-radius: 28px; position: relative;
    background: var(--glass); border: 1px solid rgba(255, 255, 255, 0.13); -webkit-backdrop-filter: var(--blur); backdrop-filter: var(--blur);
    box-shadow: var(--glass-edge), var(--glass-shadow); }
  body[data-sport=nfl] .tdtable tr:hover td { background: none; }
  body[data-sport=nfl] .tdtable td { display: block; border: 0; padding: 0; }
  body[data-sport=nfl] .tdtable td[colspan] { grid-column: 1 / -1; }
  body[data-sport=nfl] tr.value { border-color: rgba(110, 231, 176, 0.45); box-shadow: var(--glass-edge), 0 0 40px -10px rgba(110, 231, 176, 0.35); }
  body[data-sport=nfl] tr.value td, body[data-sport=nfl] tr.value td:first-child { background: none; box-shadow: none; }
}
@media (max-width: 560px) { .pc-top { grid-template-columns: 54px 1fr auto; } .pc-photo { width: 54px; height: 54px; } .ring { width: 62px; height: 62px; } }

/* card photos: clean headshot, no badge on the face; logos sit in the matchup line */
.pc-top { grid-template-columns: 72px 1fr auto; }
.pc-photo { width: 72px; height: 72px; overflow: hidden; padding: 0;
  background: radial-gradient(circle at 50% 30%, rgba(202, 172, 253, 0.45), rgba(49, 46, 114, 0.25) 60%, rgba(0, 0, 0, 0.25) 100%);
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.35), 0 0 0 2px rgba(178, 114, 251, 0.35), 0 10px 24px rgba(0, 0, 0, 0.45); }
.pc-photo img { width: 100%; height: 100%; object-fit: cover; object-position: 50% 20%; border-radius: 50%; }
.pc-meta { display: flex; flex-wrap: wrap; align-items: center; gap: 0 4px; }
.pc-meta b { color: var(--ink-2); font-weight: 600; }
img.pc-tlogo { width: 16px; height: 16px; object-fit: contain; vertical-align: -3px; }
.refresh .oddsmsg { max-width: min(70ch, 72vw); }
@media (max-width: 560px) { .pc-top { grid-template-columns: 58px 1fr auto; } .pc-photo { width: 58px; height: 58px; } }

/* refresh status: full-width glass banner under the header */
.refresh .oddsmsg { display: none; }
.wrap > .oddsmsg { display: none; position: static; max-width: none; text-align: left; margin: 0 0 16px; padding: 12px 18px; border-radius: 18px;
  font-size: 0.86rem; line-height: 1.45; color: var(--ink-2); background: linear-gradient(150deg, rgba(183, 143, 252, 0.12), rgba(255, 255, 255, 0.04));
  border: 1px solid rgba(183, 143, 252, 0.25); box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.15); -webkit-backdrop-filter: var(--blur); backdrop-filter: var(--blur); }
.wrap > .oddsmsg.on { display: block; }
.wrap > .oddsmsg.err { border-color: rgba(255, 143, 126, 0.4); color: #d4bdfd; }
.pc-meta { flex-wrap: nowrap; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; display: block; }
.pc-meta img.pc-tlogo { margin-right: 5px; }
.pc-chips .pospill { background: rgba(255, 255, 255, 0.12); color: var(--ink); font-weight: 600; }

/* league logos in the main NHL | NFL tabs */
.sportbar .sport button { gap: 10px; padding: 8px 30px 8px 10px; }
.slogo { display: grid; place-items: center; width: 34px; height: 34px; border-radius: 50%; flex: none;
  background: radial-gradient(circle at 50% 35%, #ffffff, #dedde6); box-shadow: 0 3px 10px rgba(0, 0, 0, 0.35), inset 0 -1px 0 rgba(0, 0, 0, 0.12); }
.slogo img { width: 26px; height: 26px; object-fit: contain; }
.slogo.nologo { width: 8px; height: 8px; background: rgba(255, 255, 255, 0.3); box-shadow: none; }
.sportbar .sport button[aria-pressed=false] .slogo { opacity: 0.75; filter: saturate(0.6); }
.sportbar .sport button[aria-pressed=true] .slogo { box-shadow: 0 0 0 2px rgba(255, 255, 255, 0.55), 0 4px 12px rgba(36, 35, 85, 0.45); }
@media (max-width: 560px) { .sportbar .sport button { padding: 6px 0; } .slogo { width: 28px; height: 28px; } .slogo img { width: 21px; height: 21px; } }

/* ---------- NHL games view ---------- */
.ngrid { display: grid; grid-template-columns: repeat(auto-fill, minmax(min(100%, 520px), 1fr)); gap: 18px; margin-top: 16px; }
.ngame { position: relative; display: grid; gap: 10px; padding: 18px 20px 16px; border-radius: 28px; overflow: hidden;
  background: var(--glass); border: 1px solid rgba(255, 255, 255, 0.13); -webkit-backdrop-filter: var(--blur); backdrop-filter: var(--blur);
  box-shadow: var(--glass-edge), var(--glass-shadow); }
.ngame::before { content: ""; position: absolute; inset: -40% -20% auto auto; width: 60%; height: 70%; border-radius: 50%; pointer-events: none;
  background: radial-gradient(circle, rgba(173, 104, 251, 0.14), transparent 65%); }
.ng-head { display: flex; justify-content: space-between; align-items: center; font-size: 0.8rem; }
.ng-time { font-weight: 600; padding: 4px 12px; border-radius: 999px; background: rgba(255, 255, 255, 0.08); border: 1px solid rgba(255, 255, 255, 0.1); }
.ng-time.live { background: rgba(151, 65, 250, 0.2); border-color: rgba(167, 94, 251, 0.5); color: #c5a5fd; }
.ng-team { display: grid; grid-template-columns: 44px 1fr auto auto; gap: 14px; align-items: center; }
.ng-team.lost { opacity: 0.55; }
img.ng-logo { width: 44px; height: 44px; object-fit: contain; filter: drop-shadow(0 4px 10px rgba(0, 0, 0, 0.45)); }
.ng-name b { display: block; font-weight: 600; font-size: 1.08rem; letter-spacing: -0.01em; }
.ng-name small { color: var(--muted); font-size: 0.76rem; line-height: 1.35; }
.ng-ranks { display: flex; gap: 8px; }
.rk { --h: 60; display: grid; justify-items: center; min-width: 76px; padding: 6px 10px; border-radius: 14px;
  background: hsla(var(--h), 70%, 45%, 0.16); border: 1px solid hsla(var(--h), 75%, 60%, 0.35); box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.08); }
.rk small { font-size: 0.6rem; text-transform: uppercase; letter-spacing: 0.08em; color: var(--muted); }
.rk b { font-size: 1.05rem; font-weight: 600; color: hsl(var(--h), 80%, 72%); line-height: 1.2; }
.rk em { font-style: normal; font-size: 0.64rem; color: var(--muted); }
.ng-score { font-size: 1.8rem; font-weight: 600; min-width: 2ch; text-align: right; }
.ng-goalie { display: flex; align-items: center; gap: 10px; margin: -2px 0 2px 58px; padding: 8px 12px; border-radius: 14px;
  background: rgba(0, 0, 0, 0.18); border: 1px solid rgba(255, 255, 255, 0.07); font-size: 0.8rem; }
.ng-goalie.none { color: var(--muted); }
.gmask { width: 18px; height: 18px; flex: none; border-radius: 6px; background: linear-gradient(145deg, #d3bafd, #a473dd);
  -webkit-mask: radial-gradient(circle at 50% 38%, #000 42%, transparent 44%), linear-gradient(#000 0 0) bottom/100% 45% no-repeat;
  mask: radial-gradient(circle at 50% 38%, #000 42%, transparent 44%), linear-gradient(#000 0 0) bottom/100% 45% no-repeat; opacity: 0.8; }
.gwho { display: grid; min-width: 0; }
.gwho b { font-weight: 600; } .gwho small { color: var(--muted); font-size: 0.72rem; }
.gstat { margin-left: auto; font-size: 0.7rem; font-weight: 700; padding: 3px 10px; border-radius: 999px; white-space: nowrap; }
.gstat.conf { background: rgba(110, 231, 176, 0.16); color: var(--good); border: 1px solid rgba(110, 231, 176, 0.4); }
.gstat.likely { background: rgba(167, 94, 251, 0.15); color: #b68dfc; border: 1px solid rgba(167, 94, 251, 0.4); }
.gstat.proj { background: rgba(255, 255, 255, 0.08); color: var(--ink-2); border: 1px solid rgba(255, 255, 255, 0.14); }
.ng-vs { display: flex; align-items: center; gap: 10px; color: var(--muted); font-size: 0.75rem; }
.ng-vs::before, .ng-vs::after { content: ""; flex: 1; height: 1px; background: linear-gradient(90deg, transparent, rgba(255, 255, 255, 0.12), transparent); }
.ng-lines { display: grid; grid-template-columns: 1.2fr 1fr 1.2fr 1.2fr; gap: 6px 8px; align-items: center; margin-top: 4px; padding: 12px 14px;
  border-radius: 18px; background: rgba(0, 0, 0, 0.22); border: 1px solid rgba(255, 255, 255, 0.08); font-size: 0.86rem; }
.ng-lines.empty { display: block; color: var(--muted); font-size: 0.78rem; text-align: center; }
.ngl-h { font-size: 0.6rem; text-transform: uppercase; letter-spacing: 0.08em; color: var(--muted); text-align: center; }
.ngl-h:first-child { text-align: left; }
.ngl-team { display: flex; align-items: center; gap: 8px; font-weight: 600; }
.ngl-logo { width: 22px; height: 22px; object-fit: contain; }
.ngl-cell { text-align: center; font-weight: 600; padding: 6px 4px; border-radius: 10px; background: rgba(255, 255, 255, 0.05); border: 1px solid rgba(255, 255, 255, 0.07); font-variant-numeric: tabular-nums; }
.ngl-cell em { font-style: normal; font-weight: 500; color: var(--muted); font-size: 0.8rem; margin-left: 2px; }
.ngl-cell.fav { color: #c09dfc; border-color: rgba(166, 91, 251, 0.35); }
.ngl-when { grid-column: 1 / -1; text-align: right; font-size: 0.66rem; color: var(--muted); }
.ng-props { justify-self: end; margin-top: 4px; background: rgba(152, 66, 250, 0.14); border: 1px solid rgba(166, 91, 251, 0.4); color: #c09dfc;
  border-radius: 999px; padding: 7px 14px; font: 600 0.8rem var(--body); cursor: pointer; }
.ng-props:hover { background: rgba(152, 66, 250, 0.24); }
@media (max-width: 560px) {
  .ng-team { grid-template-columns: 36px 1fr auto; } img.ng-logo { width: 36px; height: 36px; }
  .ng-ranks { grid-column: 1 / -1; } .rk { flex: 1; } .ng-goalie { margin-left: 0; } .ng-score { grid-row: 1; grid-column: 3; }
}

/* brand: logo mark + wordmark */
.brand { gap: 12px; color: var(--ink); }
.brand::before { content: none; display: none; }
.brand-mark { width: 40px; height: 40px; flex: none; filter: drop-shadow(0 6px 16px rgba(122, 31, 227, 0.45)); }
.brand-text { display: grid; line-height: 1; gap: 4px; }
.brand-name { font: 700 1.25rem/1 var(--display); letter-spacing: -0.02em; color: var(--ink); }
.brand-sub { font: 600 0.62rem/1 var(--body); letter-spacing: 0.22em; text-transform: uppercase; color: #ac7dfc; }
/* goalie headshots */
.gface { width: 36px; height: 36px; flex: none; border-radius: 50%; overflow: hidden; display: grid; place-items: center;
  font: 600 0.72rem var(--body); color: var(--ink-2);
  background: radial-gradient(circle at 50% 30%, rgba(202, 172, 253, 0.4), rgba(49, 46, 114, 0.25) 65%, rgba(0, 0, 0, 0.25));
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.3), 0 0 0 1.5px rgba(178, 114, 251, 0.35), 0 4px 10px rgba(0, 0, 0, 0.4); }
.gface img { width: 100%; height: 100%; object-fit: cover; object-position: 50% 20%; }
@media (prefers-reduced-motion: reduce) { * { transition: none !important; } }
@supports not ((backdrop-filter: blur(1px)) or (-webkit-backdrop-filter: blur(1px))) {
  .masthead, .game, .tbl, .ticket, .empty, .error, .windows, .posf, .sport, .views { background: rgba(21, 20, 40, 0.92); }
}

/* ---------- NHL tab ---------- */
.nhlbar { display: flex; flex-wrap: wrap; gap: 10px; align-items: center; margin: 14px 0 0; }
.nhlbar .lbl { font-size: 0.75rem; text-transform: uppercase; letter-spacing: 0.08em; color: var(--muted); margin-right: -2px; }
.toggle { display: inline-flex; align-items: center; gap: 8px; font-size: 0.84rem; color: var(--ink-2); cursor: pointer; user-select: none; }
.toggle input { appearance: none; width: 38px; height: 22px; border-radius: 999px; background: rgba(255, 255, 255, 0.12); border: 1px solid rgba(255, 255, 255, 0.16);
  position: relative; cursor: pointer; transition: background .2s; margin: 0; }
.toggle input::after { content: ""; position: absolute; top: 2px; left: 2px; width: 16px; height: 16px; border-radius: 50%; background: #fff; box-shadow: 0 2px 6px rgba(0,0,0,.35); transition: transform .2s; }
.toggle input:checked { background: var(--orange); border-color: rgba(189, 153, 252, 0.5); }
.toggle input:checked::after { transform: translateX(16px); }
.gamepills { display: flex; gap: 8px; overflow-x: auto; padding: 4px 2px 8px; margin-top: 12px; scrollbar-width: thin; }
.gpill { flex: none; display: grid; grid-template-columns: auto auto auto; gap: 6px; align-items: center; padding: 8px 14px; border-radius: 999px; cursor: pointer;
  background: rgba(255, 255, 255, 0.06); border: 1px solid rgba(255, 255, 255, 0.11); color: var(--ink-2); font: 600 0.82rem var(--body); box-shadow: var(--glass-edge); }
.gpill img { width: 20px; height: 20px; }
.gpill small { grid-column: 1 / -1; text-align: center; color: var(--muted); font-size: 0.7rem; margin-top: -2px; }
.gpill[aria-pressed=true] { background: rgba(152, 66, 250, 0.18); border-color: rgba(166, 91, 251, 0.5); color: var(--ink); }
.nres { display: inline-block; margin-top: 4px; font-size: 0.74rem; font-weight: 700; padding: 2px 8px; border-radius: 999px; }
.nres.win { background: rgba(110, 231, 176, 0.15); color: var(--good); } .nres.loss { background: rgba(255, 143, 126, 0.12); color: var(--bad); }
.sidepick { font-size: 0.72rem; font-weight: 700; text-transform: uppercase; letter-spacing: 0.06em; color: var(--muted); }
.statpills { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 6px; }
.statpills span { background: rgba(255, 255, 255, 0.06); border: 1px solid rgba(255, 255, 255, 0.08); border-radius: 999px; padding: 2px 9px; font-size: 0.74rem; color: var(--ink-2); }
.statpills b { color: var(--ink); }
.warnpill { color: #ac7dfc !important; border-color: rgba(166, 91, 251, 0.35) !important; background: rgba(152, 66, 250, 0.1) !important; }
.nhlsum { display: grid; grid-template-columns: repeat(auto-fit, minmax(170px, 1fr)); gap: 14px; margin-top: 18px; }
.stat { padding: 14px 18px; border-radius: var(--radius); }
.stat small { display: block; color: var(--muted); font-size: 0.74rem; text-transform: uppercase; letter-spacing: 0.08em; }
.stat b { display: block; font: 800 1.6rem/1.2 var(--display); letter-spacing: -0.02em; margin-top: 4px; }
.stat b.up { color: var(--good); text-shadow: 0 0 18px rgba(110, 231, 176, 0.3); }
input.oin[data-nm] { width: 6.5em; }
.hrline { font-size: 0.78rem; color: var(--muted); margin-bottom: 4px; }
.hrline b { font-size: 1.05rem; color: var(--ink); margin-left: 4px; }
.manrow { display: flex; gap: 6px; align-items: center; font-size: 0.82rem; color: var(--ink-2); }
.lsel { background: rgba(0, 0, 0, 0.28); border: 1px solid rgba(255, 255, 255, 0.14); border-radius: 10px; color: var(--ink); padding: 4px 6px; font: 700 0.9rem var(--body); }
.prob { grid-template-columns: auto 1fr; gap: 12px; }
.prob b { font-size: 1.35rem; white-space: nowrap; }
.ticket .val span { font-size: 0.74rem; text-align: right; }
.ticket .bet { color: var(--ink-2); }

/* ================= compact solid top bar (Oct 2026) ================= */
.masthead { background: linear-gradient(180deg, #13132d 0%, #0f0e22 100%) !important; -webkit-backdrop-filter: none !important; backdrop-filter: none !important;
  border: 1px solid rgba(183, 143, 252, 0.16); box-shadow: 0 14px 34px -14px rgba(0, 0, 0, 0.85), inset 0 1px 0 rgba(255, 255, 255, 0.08); }
@media (min-width: 861px) {
  .masthead { top: 0; margin: 0; width: 100%; max-width: none; border-radius: 0; border-width: 0 0 1px 0;
    padding: 10px max(24px, calc((100% - 1232px) / 2)) 10px; display: grid; align-items: center; column-gap: 14px; row-gap: 8px;
    grid-template-columns: auto auto auto minmax(0, auto) auto 1fr auto; }
  .mast-in, .datenav { display: contents; }
  .brand { grid-area: 1 / 1; }
  .sportbar { grid-area: 1 / 2; padding: 0; }
  #prev { grid-area: 1 / 3; } .dateblock { grid-area: 1 / 4; min-width: 0; } #next { grid-area: 1 / 5; }
  .refresh { grid-area: 1 / 7; }
  .navrow { grid-area: 2 / 1 / 3 / 6; padding: 0; min-width: 0; }
  .datetools { grid-area: 2 / 6 / 3 / 8; justify-self: end; margin: 0; }
  .brand-mark { width: 32px; height: 32px; }
  .brand-name { font-size: 1.05rem; } .brand-sub { font-size: 0.54rem; letter-spacing: 0.2em; }
  .sportbar .sport { padding: 3px; gap: 2px; }
  .sportbar .sport button { padding: 4px 16px 4px 4px; font-size: 0.86rem; gap: 8px; }
  .slogo { width: 26px; height: 26px; } .slogo img { width: 19px; height: 19px; }
  .dateline { font-size: 1.22rem !important; line-height: 1.1; }
  .slate { font-size: 0.74rem; }
  .arrow, .settings summary { width: 32px; height: 32px; }
  button.primary { padding: 7px 18px; font-size: 0.88rem; }
  .views { padding: 3px; }
  .tabs button { padding: 6px 14px; font-size: 0.84rem; }
  .ghost, .datetools input[type=date] { padding: 6px 12px; font-size: 0.8rem; }
  .datetools input[type=date] { padding: 5px 10px; }
  html { scroll-padding-top: 120px; }
  .wrap { padding-top: 18px; }
}
@media (min-width: 861px) and (max-width: 1100px) { .brand-text { display: none; } .brand { display: flex !important; } }

/* ================= neon night theme (Oct 2026): navy/charcoal, violet + mint + magenta ================= */
:root {
  --bg: #0c0c18; --ink: #eeedf7; --ink-2: #cfcde3; --muted: rgba(226, 224, 245, 0.56);
  --orange: linear-gradient(135deg, #a78bfa 0%, #8b5cf6 45%, #d946ef 100%);
  --turf: #a78bfa; --amber: #c4b5fd; --amber-soft: rgba(139, 92, 246, 0.16);
  --good: #4ade9f; --bad: #fb7185; --turf-soft: rgba(74, 222, 159, 0.14);
  --glass: linear-gradient(155deg, rgba(58, 56, 92, 0.46) 0%, rgba(26, 25, 44, 0.62) 55%, rgba(34, 30, 60, 0.56) 100%);
  --glass-edge: inset 0 1px 0 rgba(255, 255, 255, 0.10), inset 0 -1px 0 rgba(0, 0, 0, 0.35), inset 1px 0 0 rgba(255, 255, 255, 0.04);
  --glass-shadow: 0 24px 60px -24px rgba(0, 0, 0, 0.85), 0 2px 10px rgba(0, 0, 0, 0.35);
}
html, body { background: #0c0c18; }
body::after { background:
    radial-gradient(30% 32% at 12% 8%, rgba(139, 92, 246, 0.30), transparent 70%),
    radial-gradient(26% 30% at 88% 14%, rgba(45, 212, 191, 0.18), transparent 72%),
    radial-gradient(40% 30% at 60% 104%, rgba(217, 70, 239, 0.26), transparent 70%),
    radial-gradient(24% 26% at 4% 72%, rgba(59, 130, 246, 0.16), transparent 72%),
    radial-gradient(26% 28% at 97% 70%, rgba(168, 85, 247, 0.18), transparent 72%),
    linear-gradient(180deg, #13132a 0%, #0e0e1d 45%, #09090f 100%) !important; }
.masthead { background: linear-gradient(180deg, #17162b 0%, #121124 100%) !important; border-color: rgba(167, 139, 250, 0.20) !important;
  box-shadow: 0 14px 34px -14px rgba(0, 0, 0, 0.9), inset 0 1px 0 rgba(255, 255, 255, 0.06), 0 1px 0 rgba(139, 92, 246, 0.25) !important; }
button.primary, .sport button[aria-pressed=true] { color: #fff !important; border-color: rgba(216, 180, 254, 0.55);
  box-shadow: 0 10px 28px -8px rgba(168, 85, 247, 0.75), inset 0 1px 0 rgba(255, 255, 255, 0.35); text-shadow: 0 1px 2px rgba(40, 0, 80, 0.4); }
button.primary:hover { box-shadow: 0 14px 34px -8px rgba(217, 70, 239, 0.8), inset 0 1px 0 rgba(255, 255, 255, 0.4); }
.sportbar .sport button[aria-pressed=true] .slogo { box-shadow: 0 0 0 2px rgba(255, 255, 255, 0.6), 0 4px 12px rgba(60, 20, 120, 0.5); }
.tabs button[aria-pressed=true]::before { background: #2dd4bf; box-shadow: 0 0 8px #2dd4bf; }
.tabs button[aria-pressed=true] { background: rgba(139, 92, 246, 0.22); }
.gpill[aria-pressed=true], .lupill { background: rgba(139, 92, 246, 0.18) !important; border-color: rgba(167, 139, 250, 0.5) !important; color: #ddd6fe !important; }
.stat b.up { color: #4ade9f; text-shadow: 0 0 18px rgba(74, 222, 159, 0.45); }
.pbar i { background: linear-gradient(90deg, #8b5cf6, #d946ef); box-shadow: 0 0 12px rgba(168, 85, 247, 0.55); }
.ticket::before { background: linear-gradient(90deg, #8b5cf6, #2dd4bf); }
.toggle input:checked { background: linear-gradient(135deg, #8b5cf6, #d946ef); }
a { color: #c4b5fd; }
</style>
</head>
<body data-sport="nhl">
<header class="masthead">
  <div class="sportbar" role="tablist" aria-label="Sport">
    <div class="sport">
      <button data-sport="nhl" role="tab" aria-pressed="false"><span class="slogo"><img src="https://a.espncdn.com/i/teamlogos/leagues/500/nhl.png" alt="" onerror="this.parentNode.classList.add('nologo');this.remove()"></span>NHL</button>
      <button data-sport="nfl" role="tab" aria-pressed="true"><span class="slogo"><img src="https://a.espncdn.com/i/teamlogos/leagues/500/nfl.png" alt="" onerror="this.parentNode.classList.add('nologo');this.remove()"></span>NFL</button>
    </div>
  </div>
  <div class="mast-in">
    <div class="brand" aria-label="GameDay Edge Board">
      <svg class="brand-mark" viewBox="0 0 40 40" aria-hidden="true">
        <defs><linearGradient id="bm" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#a78bfa"/><stop offset="1" stop-color="#d946ef"/></linearGradient></defs>
        <rect x="1" y="1" width="38" height="38" rx="11" fill="url(#bm)"/>
        <rect x="1.5" y="1.5" width="37" height="37" rx="10.5" fill="none" stroke="rgba(255,255,255,.45)" stroke-width="1"/>
        <path d="M9 27.5 L16 20.5 L21 24.5 L31 13" fill="none" stroke="#140a2a" stroke-width="3.2" stroke-linecap="round" stroke-linejoin="round"/>
        <path d="M25.5 12.5 H31.5 V18.5" fill="none" stroke="#140a2a" stroke-width="3.2" stroke-linecap="round" stroke-linejoin="round"/>
      </svg>
      <span class="brand-text"><span class="brand-name">GameDay</span><span class="brand-sub">Edge Board</span></span>
    </div>
    <div class="datenav">
      <button id="prev" class="arrow" aria-label="Previous day">‹</button>
      <div class="dateblock"><div class="dateline" id="dateline"></div><div class="slate" id="slate"></div></div>
      <button id="next" class="arrow" aria-label="Next day">›</button>
      <div class="datetools">
        <input type="date" id="date" aria-label="Pick a date">
        <button id="today" class="ghost">Today</button>
        <button id="nextGames" class="ghost">Next game day</button>
      </div>
    </div>
    <div class="refresh">
      <button id="loadOdds" class="primary">Refresh</button>
      <details class="settings">
        <summary aria-label="Odds settings" title="Odds settings">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true"><circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.7 1.7 0 0 0 .3 1.8l.1.1a2 2 0 1 1-2.8 2.8l-.1-.1a1.7 1.7 0 0 0-1.8-.3 1.7 1.7 0 0 0-1 1.5V21a2 2 0 1 1-4 0v-.1a1.7 1.7 0 0 0-1.1-1.5 1.7 1.7 0 0 0-1.8.3l-.1.1a2 2 0 1 1-2.8-2.8l.1-.1a1.7 1.7 0 0 0 .3-1.8 1.7 1.7 0 0 0-1.5-1H3a2 2 0 1 1 0-4h.1a1.7 1.7 0 0 0 1.5-1.1 1.7 1.7 0 0 0-.3-1.8l-.1-.1a2 2 0 1 1 2.8-2.8l.1.1a1.7 1.7 0 0 0 1.8.3h.1a1.7 1.7 0 0 0 1-1.5V3a2 2 0 1 1 4 0v.1a1.7 1.7 0 0 0 1 1.5 1.7 1.7 0 0 0 1.8-.3l.1-.1a2 2 0 1 1 2.8 2.8l-.1.1a1.7 1.7 0 0 0-.3 1.8v.1a1.7 1.7 0 0 0 1.5 1H21a2 2 0 1 1 0 4h-.1a1.7 1.7 0 0 0-1.5 1z"/></svg>
        </summary>
        <div class="settings-panel">
          <label>Odds API key <input type="password" id="apiKey" autocomplete="off" placeholder="Paste your key once"></label>
          <label>Sportsbook <select id="bookSel">
            <option value="hardrockbet_fl">Hard Rock Bet (FL)</option>
            <option value="hardrockbet">Hard Rock Bet (IN and other states)</option>
            <option value="hardrockbet_az">Hard Rock Bet (AZ)</option>
            <option value="hardrockbet_oh">Hard Rock Bet (OH)</option>
          </select></label>
          <p>Refresh loads the latest NFL and NHL stats, injury reports and this day's Hard Rock props (about 5 credits per NFL game, 1 per NHL game).</p>
        </div>
      </details>
    </div>
  </div>
  <div class="navrow">
    <nav class="tabs views" aria-label="View">
      <button class="nfl-only" data-v="games" aria-pressed="true">Games</button>
      <button class="nfl-only" data-v="td" aria-pressed="false">Touchdown Scorers</button>
      <button class="nfl-only" data-v="yds" aria-pressed="false">Yards</button>
      <button class="nfl-only" data-v="vol" aria-pressed="false">Receptions &amp; Rush Attempts</button>
      <button class="nhl-only" data-v="nhl_games" aria-pressed="false">Games</button>
      <button class="nhl-only" data-v="nhl_pts" aria-pressed="false">Points</button>
      <button class="nhl-only" data-v="nhl_sog" aria-pressed="false">Shots</button>
    </nav>
  </div>
</header>
<div class="wrap">
  <div class="oddsmsg" id="oddsMsg" role="status"></div>
  <div class="toolbar nfl-only">
    <div class="windows" role="group" aria-label="Kickoff window">
      <button data-w="all" aria-pressed="true">All day</button>
      <button data-w="early" aria-pressed="false">Early</button>
      <button data-w="late" aria-pressed="false">Late afternoon</button>
      <button data-w="night" aria-pressed="false">Night</button>
    </div>
    <div class="controls">
      <button id="expand">Open all TD outlooks</button>
      <button id="exportTD">Export CSV</button>
      <button id="exportPlayers">Export players CSV</button>
      <button id="export">Export games CSV</button>
    </div>
  </div>
  <details class="howto"><summary>How to read this board</summary><p class="note" id="note"></p></details>
  <main id="board"></main>
</div>

<script type="application/json" id="nfl-data">__DATA__</script>
<script>
const D = JSON.parse(document.getElementById("nfl-data").textContent);
const ET = "America/New_York";
const POSITIONS = ["QB", "RB", "WR", "TE"];
// Stat slots in each player-game row (after day, game id, team, opponent, player id)
const S = { cmp: 0, att: 1, pyd: 2, ptd: 3, int: 4, car: 5, ryd: 6, rtd: 7, tgt: 8, rec: 9, reyd: 10, retd: 11 };
const state = { date: todayET(), windowKey: "all", openAll: false, view: "games", tdPos: "All", tdSort: "chance",
  ydsStat: "rec_yds", volStat: "rec", propSort: "edge", propPos: "All" };
const $ = (id) => document.getElementById(id);

/* ---------- helpers ---------- */
function todayET() { return new Intl.DateTimeFormat("en-CA", { timeZone: ET, year: "numeric", month: "2-digit", day: "2-digit" }).format(new Date()); }
function shiftDate(ymd, n) { const [y, m, d] = ymd.split("-").map(Number); return new Date(Date.UTC(y, m - 1, d + n)).toISOString().slice(0, 10); }
function prettyDate(ymd) { const [y, m, d] = ymd.split("-").map(Number);
  return new Date(Date.UTC(y, m - 1, d, 12)).toLocaleDateString("en-US", { timeZone: "UTC", weekday: "long", month: "long", day: "numeric", year: "numeric" }); }
function prettyTime(hhmm) { const [h, m] = hhmm.split(":").map(Number); return `${h % 12 || 12}:${String(m).padStart(2, "0")} ${h < 12 ? "AM" : "PM"}`; }
function windowOf(hhmm) { const h = Number(hhmm.split(":")[0]); return h < 16 ? "early" : h < 18 ? "late" : "night"; }
function esc(s) { return String(s ?? "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c])); }
const f0 = (v) => Math.round(v).toString(), f1 = (v) => v.toFixed(1);
const team = (abbr) => ({ abbr, name: D.teams[abbr]?.[0] || abbr, logo: D.teams[abbr]?.[1] || "" });
function rankMap(obj, higherFirst) {
  const vals = Object.values(obj).sort((a, b) => higherFirst ? b - a : a - b);
  return Object.fromEntries(Object.entries(obj).map(([k, v]) => [k, vals.indexOf(v) + 1]));
}

/* ---------- stats as of a date (only games played before it) ---------- */
const DVP = {
  QB: { label: "Pass yds", val: (s) => s[S.pyd], extra: (s) => `${f1(s[S.ptd])} pass TD, ${f0(s[S.ryd])} rush yds` },
  RB: { label: "Scrimmage yds", val: (s) => s[S.ryd] + s[S.reyd], extra: (s) => `${f0(s[S.ryd])} rush, ${f1(s[S.rec])} rec for ${f0(s[S.reyd])}, ${f1(s[S.rtd] + s[S.retd])} TD` },
  WR: { label: "Rec yds", val: (s) => s[S.reyd], extra: (s) => `${f1(s[S.rec])} rec on ${f1(s[S.tgt])} tgt, ${f1(s[S.retd])} TD` },
  TE: { label: "Rec yds", val: (s) => s[S.reyd], extra: (s) => `${f1(s[S.rec])} rec on ${f1(s[S.tgt])} tgt, ${f1(s[S.retd])} TD` },
};
const ctxCache = new Map();
function context(ymd) {
  if (ctxCache.has(ymd)) return ctxCache.get(ymd);
  const played = D.games.filter((g) => g.type === "REG" && g.day < ymd && g.hs !== null);
  const tot = {}, lastGame = {};
  for (const g of played) {
    for (const [t, f, a] of [[g.home, g.hs, g.as], [g.away, g.as, g.hs]]) {
      const r = (tot[t] ??= { gp: 0, pf: 0, pa: 0, w: 0, l: 0, t: 0 });
      r.gp++; r.pf += f; r.pa += a; f > a ? r.w++ : f < a ? r.l++ : r.t++;
      lastGame[t] = g.id; // games are sorted by date
    }
  }
  const off = rankMap(Object.fromEntries(Object.entries(tot).map(([t, r]) => [t, r.pf / r.gp])), true);
  const def = rankMap(Object.fromEntries(Object.entries(tot).map(([t, r]) => [t, r.pa / r.gp])), false);
  const teams = {};
  for (const [t, r] of Object.entries(tot)) teams[t] = { off: off[t], def: def[t], ppgF: r.pf / r.gp, ppgA: r.pa / r.gp,
    record: `${r.w}-${r.l}${r.t ? "-" + r.t : ""}`, gp: r.gp };

  const playedIds = new Set(played.map((g) => g.id));
  const dsum = {}, players = {}, teamTgt = {};
  for (const r of D.pw) {
    if (!playedIds.has(r[1])) continue;
    const pos = D.players[r[4]][1], s = r.slice(5);
    const d = ((dsum[r[3]] ??= {})[pos] ??= new Array(12).fill(0));
    s.forEach((v, i) => (d[i] += v));
    (players[r[4]] ??= { id: r[4], name: D.players[r[4]][0], pos, rows: [] }).rows.push(r);
    teamTgt[r[2]] = (teamTgt[r[2]] || 0) + s[S.tgt];
  }

  // Defense vs position: per-game amounts allowed, ranked 1 (allows least) to 32 (allows most)
  const dvp = {};
  for (const pos of POSITIONS) {
    const vals = {};
    for (const [d, byPos] of Object.entries(dsum)) {
      if (!teams[d]) continue;
      const pg = (byPos[pos] || new Array(12).fill(0)).map((v) => v / teams[d].gp);
      (dvp[d] ??= {})[pos] = { pg, val: DVP[pos].val(pg) };
      vals[d] = DVP[pos].val(pg);
    }
    const rk = rankMap(vals, false);
    for (const d of Object.keys(vals)) dvp[d][pos].rank = rk[d];
  }

  const byTeam = {};
  for (const p of Object.values(players)) {
    const last = p.rows[p.rows.length - 1];
    p.team = last[2];
    p.n = p.rows.length;
    const sum = (rows) => rows.reduce((acc, r) => acc.map((v, i) => v + r[5 + i]), new Array(12).fill(0));
    p.sum = sum(p.rows);
    p.avg = p.sum.map((v) => v / p.n);
    const l3 = p.rows.slice(-3);
    p.l3 = sum(l3).map((v) => v / l3.length);
    p.missedLast = lastGame[p.team] && last[1] !== lastGame[p.team];
    p.tgtShare = teamTgt[p.team] ? p.sum[S.tgt] / teamTgt[p.team] : 0;
    (byTeam[p.team] ??= []).push(p);
  }
  const ctx = { teams, dvp, byTeam };
  ctxCache.set(ymd, ctx);
  return ctx;
}

function keyPlayers(ctx, abbr) {
  const list = ctx.byTeam[abbr] || [];
  const top = (pos, key, n) => list.filter((p) => p.pos === pos && key(p.sum) > 0).sort((a, b) => key(b.sum) - key(a.sum)).slice(0, n);
  return [...top("QB", (s) => s[S.att], 1), ...top("RB", (s) => s[S.car] + s[S.tgt], 2),
          ...top("WR", (s) => s[S.tgt], 3), ...top("TE", (s) => s[S.tgt], 2)];
}
const MAIN = { QB: ["Pass yds", S.pyd], RB: ["Rush yds", S.ryd], WR: ["Rec yds", S.reyd], TE: ["Rec yds", S.reyd] };
function playerExtra(p) {
  const a = p.avg;
  if (p.pos === "QB") return `${f1(a[S.cmp])}/${f1(a[S.att])} cmp/att, ${f1(a[S.ptd])} TD, ${f1(a[S.int])} INT, ${f0(a[S.ryd])} rush yds`;
  if (p.pos === "RB") return `${f1(a[S.car])} car, ${f1(a[S.rec])} rec for ${f0(a[S.reyd])}, ${f1(a[S.rtd] + a[S.retd])} TD`;
  return `${f1(a[S.rec])} rec on ${f1(a[S.tgt])} tgt, ${Math.round(p.tgtShare * 100)}% tgt share, ${f1(a[S.retd])} TD`;
}

/* ---------- games ---------- */
function gamesOn(ymd) {
  const ctx = context(ymd);
  return D.games.filter((g) => g.day === ymd).map((g) => ({ ...g, ctx,
    A: { ...team(g.away), rank: ctx.teams[g.away] || {} }, H: { ...team(g.home), rank: ctx.teams[g.home] || {} } }));
}
function visibleGames() {
  const gs = gamesOn(state.date);
  return state.windowKey === "all" ? gs : gs.filter((g) => windowOf(g.time) === state.windowKey);
}
function nextGameDay(from) { return D.games.map((g) => g.day).find((d) => d > from); }

/* ---------- render ---------- */
function teamChip(r) {
  if (!r) return `<span class="chip na" title="No games played yet">–</span>`;
  return `<span class="chip" style="--h:${Math.round(145 * (32 - r) / 31)}" title="Rank ${r} of 32">${r}</span>`;
}
// Matchup chip: 32 = defense allows the most = best matchup for the offense (green)
function matchChip(r) {
  if (!r) return `<span class="chip na" title="No games played yet">–</span>`;
  return `<span class="chip" style="--h:${Math.round(145 * (r - 1) / 31)}" title="Allows the ${ord(33 - r)} most of 32">${r}</span>`;
}
function ord(n) { const s = ["th", "st", "nd", "rd"], v = n % 100; return n + (s[(v - 20) % 10] || s[v] || s[0]); }

function lane(o, d) {
  const or = o.rank.off, dr = d.rank.def;
  let meter = "", edge = "No games played yet this season";
  if (or && dr) {
    const diff = dr - or, pct = Math.min(100, Math.abs(diff) / 31 * 100);
    meter = `<div class="meter" aria-hidden="true"><div class="l">${diff < 0 ? `<i style="width:${pct}%;background:var(--bad)"></i>` : ""}</div>
      <div>${diff > 0 ? `<i style="width:${pct}%;background:var(--good)"></i>` : ""}</div></div>`;
    edge = diff > 0 ? `${esc(o.abbr)} offense has the edge by ${diff}` : diff < 0 ? `${esc(d.abbr)} defense has the edge by ${-diff}` : "Even matchup";
  }
  return `<div class="lane">
    <div class="side">${teamChip(or)}<span>${esc(o.abbr)} offense<br><span class="ppg">${o.rank.ppgF != null ? f1(o.rank.ppgF) + " pts scored" : ""}</span></span></div>
    <span class="vs">vs</span>
    <div class="side right"><span>${esc(d.abbr)} defense<br><span class="ppg">${d.rank.ppgA != null ? f1(d.rank.ppgA) + " pts allowed" : ""}</span></span>${teamChip(dr)}</div>
    ${meter}<div class="edge">${edge}</div></div>`;
}

function teamRow(t, g, qb, score, oppScore) {
  const final = g.hs !== null, lost = final && score < oppScore;
  const logo = t.logo ? `<img src="${esc(t.logo)}" alt="" loading="lazy" onerror="this.style.visibility='hidden'">` : `<span class="ph"></span>`;
  return `<div class="team${lost ? " lost" : ""}">${logo}
    <div><span class="name">${esc(t.name)}</span>${t.rank.record ? `<span class="rec">${t.rank.record}</span>` : ""}${qb ? `<span class="rec">QB ${esc(qb)}</span>` : ""}</div>
    <div class="score">${final ? score : ""}</div></div>`;
}

function gameLine(g) {
  const bits = [];
  if (g.spread != null) bits.push(g.spread === 0 ? "<b>Pick'em</b>" : `Spread <b>${esc(g.spread > 0 ? g.home : g.away)} −${Math.abs(g.spread)}</b>`);
  if (g.total != null) bits.push(`Total <b>${g.total}</b>`);
  if (g.stadium) bits.push(esc(g.stadium) + (g.roof && g.roof !== "outdoors" ? ` (${esc(g.roof)})` : ""));
  if (g.temp != null) bits.push(`${g.temp}°F`);
  if (g.wind != null) bits.push(`Wind ${g.wind} mph`);
  return bits.length ? `<div class="line">${bits.map((b) => `<span>${b}</span>`).join("")}</div>` : "";
}

function dvpTable(ctx, def) {
  const rows = POSITIONS.map((pos) => {
    const x = ctx.dvp[def]?.[pos];
    return `<tr><td><span class="pos">${pos}</span></td>
      <td class="num">${x ? f0(x.val) : "–"}<span class="sub">${x ? DVP[pos].label + " per game" : ""}</span></td>
      <td>${x ? `<span class="sub" style="font-size:.85rem">${DVP[pos].extra(x.pg)}</span>` : ""}</td>
      <td>${matchChip(x?.rank)}</td></tr>`;
  }).join("");
  return `<div class="tbl"><table><thead><tr><th>vs</th><th>Allowed</th><th>Also allows per game</th><th>Rank</th></tr></thead><tbody>${rows}</tbody></table></div>`;
}

function trend(avg, l3) {
  if (!avg) return "";
  const d = (l3 - avg) / Math.max(avg, 1);
  return d > 0.15 ? ` <span class="up" title="Last 3 games above season average">▲</span>` : d < -0.15 ? ` <span class="down" title="Last 3 games below season average">▼</span>` : "";
}

function playersTable(ctx, off, def, listedQB) {
  const ps = keyPlayers(ctx, off);
  if (!ps.length) return `<p class="note">No player stats yet this season.</p>`;
  const rows = ps.map((p) => {
    const [label, i] = MAIN[p.pos], m = ctx.dvp[def]?.[p.pos];
    return `<tr><td><span class="pos">${p.pos}</span>${esc(p.name)}${p.missedLast ? ` <span class="flag">Missed last game</span>` : ""}${p.pos === "QB" && listedQB && listedQB !== p.name ? ` <span class="flag">Listed starter: ${esc(listedQB)}</span>` : ""}
        <span class="sub">${playerExtra(p)}</span></td>
      <td class="num">${f1(p.avg[i])}<span class="sub">${label}, ${p.n} g</span></td>
      <td class="num">${f1(p.l3[i])}${trend(p.avg[i], p.l3[i])}<span class="sub">last ${Math.min(3, p.n)}</span></td>
      <td>${matchChip(m?.rank)}</td></tr>`;
  }).join("");
  return `<div class="tbl"><table><thead><tr><th>Player (season averages)</th><th>Avg</th><th>Recent</th><th>Matchup</th></tr></thead><tbody>${rows}</tbody></table></div>`;
}

function propsPanel(g) {
  const td = tdPanel(g);
  if (!td) return "";
  return `<details class="props"${state.openAll ? " open" : ""}><summary>Touchdown outlook</summary>${td}</details>`;
}

function gameCard(g) {
  const label = g.type === "REG" ? `Week ${g.week}` : ({ WC: "Wild Card", DIV: "Divisional", CON: "Conference", SB: "Super Bowl" }[g.type] || g.type);
  const final = g.hs !== null;
  return `<article class="game ${final ? "final" : ""}">
    <div class="meta">${final ? `Final, ${label}` : `Kickoff ${prettyTime(g.time)} ET, ${label}`}</div>
    ${teamRow(g.A, g, g.aqb, g.as, g.hs)}${teamRow(g.H, g, g.hqb, g.hs, g.as)}
    ${gameLine(g)}
    <div class="lanes">${lane(g.A, g.H)}${lane(g.H, g.A)}</div>
    ${propsPanel(g)}
  </article>`;
}

/* ---------- touchdown outlook ---------- */
function fairOdds(p) {
  if (p <= 0 || p >= 1) return "";
  return p >= 0.5 ? `−${Math.round(100 * p / (1 - p))}` : `+${Math.round(100 * (1 - p) / p)}`;
}
/* ---------- live sportsbook odds (The Odds API, fetched from this page) ---------- */
const ODDS_BASE = "https://api.the-odds-api.com/v4/sports/americanfootball_nfl";
const BOOKS = { hardrockbet_fl: "Hard Rock Bet (FL)", hardrockbet: "Hard Rock Bet", hardrockbet_az: "Hard Rock Bet (AZ)", hardrockbet_oh: "Hard Rock Bet (OH)" };
const store = {
  get(k, fallback) { try { const v = localStorage.getItem(k); return v == null ? fallback : JSON.parse(v); } catch (e) { return fallback; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) { /* storage unavailable */ } },
};
let liveOdds = store.get("nflBoard.liveOdds", {});   // {gameId: {book, fetched, prices: {pid: price}, extra: [[name, price]]}}
let oddsMsg = { text: "", err: false };
function normName(n) {
  return (n || "").normalize("NFKD").replace(/[\u0300-\u036f]/g, "").toLowerCase().replace(/[^a-z0-9 ]/g, " ")
    .split(/\s+/).filter((w) => w && !["jr", "sr", "ii", "iii", "iv", "v"].includes(w)).join(" ");
}
function currentBook() { return $("bookSel").value; }
function liveFor(gid) { const x = liveOdds[gid]; return x && x.book === currentBook() ? x : null; }

let served = false, serverHasKey = false;
async function detectServer() {
  if (!location.protocol.startsWith("http")) return;
  try {
    const r = await fetch("/api/status", { cache: "no-store" });
    if (!r.ok) return;
    const st = await r.json();
    served = !!st.served; serverHasKey = !!st.hasKey;
    if (st.book) $("bookSel").value = st.book;
    $("apiKey").placeholder = serverHasKey ? "Key saved on this computer" : "Paste your key once";
    $("apiKey").value = "";
  } catch (e) { /* opened as a plain file */ }
}
async function saveKey() {
  const key = $("apiKey").value.trim();
  if (served) {
    const r = await fetch("/api/settings", { method: "POST", headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ odds_key: key, book: currentBook() }) });
    const st = await r.json();
    serverHasKey = !!st.hasKey; $("apiKey").value = "";
    $("apiKey").placeholder = serverHasKey ? "Key saved on this computer" : "Paste your key once";
    oddsMsg = { text: serverHasKey ? "Key saved. It will load automatically from now on." : "Key removed.", err: false };
  } else {
    store.set("nflBoard.oddsApiKey", key);
    oddsMsg = { text: key ? "Key saved in this browser." : "Key removed.", err: false };
  }
  render();
}
async function refreshAll() {
  if (!served && D.shared && !$("apiKey").value.trim()) {
    // shared web link: the board is rebuilt in the cloud, so Refresh just loads the newest published copy
    sessionStorage.setItem("nflBoard.lastMsg", `Loaded the latest board (built ${D.generated}). ${D.shared.note}`);
    location.replace(location.pathname + "?t=" + Date.now() + location.hash);
    return;
  }
  if (!served) return loadAllOdds();
  const btn = $("loadOdds");
  btn.disabled = true; btn.textContent = "Refreshing…";
  oddsMsg = { text: `Downloading the latest stats, injury reports${serverHasKey ? " and Hard Rock NFL and NHL props for this day" : ""}. This takes about 30–60 seconds.`, err: false };
  render();
  try {
    const r = await fetch("/api/refresh", { method: "POST", headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ date: state.date, book: currentBook(), odds: serverHasKey }) });
    const res = await r.json();
    if (!res.ok) throw new Error(res.message || "Refresh failed");
    sessionStorage.setItem("nflBoard.lastMsg", "Refreshed. " + (res.message || (serverHasKey ? "" : "Save your Odds API key to include Hard Rock odds.")));
    location.hash = state.date;
    location.reload();
  } catch (e) {
    oddsMsg = { text: e.message.includes("fetch") ? "Lost connection to the board. Is the Start NFL Board window still open?" : e.message, err: true };
    btn.disabled = false; btn.textContent = "Refresh";
    render();
  }
}

async function oddsEvents(base, key) {
  const r = await fetch(`${base}/events?apiKey=${encodeURIComponent(key)}`);
  if (r.status === 401) throw new Error("The Odds API rejected this key. Check that it's a key from the-odds-api.com");
  if (!r.ok) throw new Error(`The Odds API returned ${r.status}`);
  return r.json();
}
let oddsRemaining = null;
async function loadNflOdds(key, book) {
    const games = gamesOn(state.date).filter((g) => g.hs === null);
    if (!games.length) return "";
    const events = await oddsEvents(ODDS_BASE, key);
    let priced = 0, withBook = 0;
    for (const g of games) {
      const home = D.teams[g.home]?.[0], away = D.teams[g.away]?.[0];
      const ev = events.find((e) => e.home_team === home && e.away_team === away &&
        new Intl.DateTimeFormat("en-CA", { timeZone: ET }).format(new Date(e.commence_time)) === g.day);
      if (!ev) continue;
      const url = `${ODDS_BASE}/events/${ev.id}/odds?apiKey=${encodeURIComponent(key)}&bookmakers=${book}&markets=player_anytime_td,player_reception_yds,player_receptions,player_rush_yds,player_rush_attempts&oddsFormat=american`;
      const r = await fetch(url);
      oddsRemaining = r.headers.get("x-requests-remaining") ?? oddsRemaining;
      if (r.status === 429) throw new Error("Out of Odds API credits for this month");
      if (!r.ok) continue;
      priced++;
      const data = await r.json();
      const rows = D.td?.[g.id] || [];
      const byName = Object.fromEntries(rows.map((x) => [normName(x.name), x.pid]));
      const entry = { book, fetched: new Date().toISOString(), prices: {}, extra: [], props: {} };
      const propByName = Object.fromEntries((D.props?.[g.id] || []).map((x) => [normName(x.name), x.pid]));
      const MK = { player_reception_yds: "rec_yds", player_receptions: "rec", player_rush_yds: "rush_yds", player_rush_attempts: "rush_att" };
      for (const bm of data.bookmakers || []) for (const m of bm.markets || []) {
        if (MK[m.key]) {
          for (const o of m.outcomes || []) {
            const pid = propByName[normName(o.description)];
            if (!pid || o.point == null || !["Over", "Under"].includes(o.name)) continue;
            const slot = ((entry.props[MK[m.key]] ??= {})[pid] ??= [o.point, null, null]);
            if (slot[0] === o.point) slot[o.name === "Over" ? 1 : 2] = Math.round(o.price);
          }
          continue;
        }
        if (m.key !== "player_anytime_td") continue;
        for (const o of m.outcomes || []) {
          if (o.name === "No" || o.name === "Under" || o.price == null) continue;
          const who = o.description || o.name, pid = byName[normName(who)];
          if (pid) entry.prices[pid] = Math.round(o.price); else entry.extra.push([who, Math.round(o.price)]);
        }
      }
      if (Object.keys(entry.prices).length || entry.extra.length || Object.keys(entry.props).length) withBook++;
      liveOdds[g.id] = entry;
    }
    store.set("nflBoard.liveOdds", liveOdds);
    return `NFL: ${BOOKS[book]} odds for ${withBook} of ${games.length} game${games.length > 1 ? "s" : ""}` +
      (priced > withBook ? ` (${priced - withBook} not posted yet).` : ".");
}

const NHL_ODDS_BASE = "https://api.the-odds-api.com/v4/sports/icehockey_nhl";
const NHL_MARKETS = { player_points: "pts", player_shots_on_goal: "sog" };
const NHL_STAT = { pts: { label: "Points", unit: "pts", lines: [0.5, 1.5, 2.5] }, sog: { label: "Shots on goal", unit: "SOG", lines: [0.5, 1.5, 2.5, 3.5, 4.5, 5.5] } };
let nhlLive = store.get("nhlBoard.liveOdds", {});   // {gameId: {book, fetched, props: {pid: {pts: [[line, over, under], ...]}}}}
function nhlPidByName(g, who) {
  const rows = D.nhl?.proj?.[g.id] || [], n = normName(who), parts = n.split(" ");
  const exact = rows.find((x) => normName(x.name) === n);
  if (exact) return exact.pid;
  const c = rows.filter((x) => { const q = normName(x.name).split(" "); return q[q.length - 1] === parts[parts.length - 1] && q[0][0] === parts[0][0]; });
  return c.length === 1 ? c[0].pid : null;
}
let nhlGameLinesLive = store.get("nhlBoard.gameLines", {});   // {gameId: {ml, pl, tot, book, fetched}}
async function loadNhlGameLines(key, book) {
  // Moneyline, puck line and total for every upcoming NHL game in ONE request (about 3 credits)
  const today = new Intl.DateTimeFormat("en-CA", { timeZone: ET }).format(new Date());
  const games = (D.nhl?.games || []).filter((g) => g.day >= today);
  if (!games.length) return 0;
  const order = [book, "hardrockbet", ...Object.keys(BOOKS)].filter((k, i, a) => a.indexOf(k) === i);
  const r = await fetch(`${NHL_ODDS_BASE}/odds?apiKey=${encodeURIComponent(key)}&bookmakers=${order.join(",")}&markets=h2h,spreads,totals&oddsFormat=american`);
  oddsRemaining = r.headers.get("x-requests-remaining") ?? oddsRemaining;
  if (r.status === 429) throw new Error("Out of Odds API credits for this month");
  if (!r.ok) return 0;
  const teamOf = (full) => {
    const n = normName(full);
    for (const g of games) for (const t of [g.home, g.away]) {
      const tn = normName(D.nhl.teams?.[t]?.[0] || t);
      if (tn === n || tn.split(" ").pop() === n.split(" ").pop()) return t;
    }
    return null;
  };
  let n = 0;
  for (const ev of await r.json()) {
    const day = new Intl.DateTimeFormat("en-CA", { timeZone: ET }).format(new Date(ev.commence_time));
    const h = teamOf(ev.home_team), a = teamOf(ev.away_team);
    const g = games.find((x) => x.day === day && x.home === h && x.away === a);
    if (!g) continue;
    const byBook = Object.fromEntries((ev.bookmakers || []).map((b) => [b.key, b]));
    const e = {};
    for (const k of order) {
      const bm = byBook[k]; if (!bm) continue;
      for (const m of bm.markets || []) {
        const oc = m.outcomes || [];
        if (m.key === "h2h" && !e.ml) e.ml = Object.fromEntries(oc.map((o) => [teamOf(o.name), o.price]).filter((x) => x[0]));
        if (m.key === "spreads" && !e.pl) e.pl = Object.fromEntries(oc.map((o) => [teamOf(o.name), [o.point, o.price]]).filter((x) => x[0]));
        if (m.key === "totals" && !e.tot) {
          const ov = oc.find((o) => o.name === "Over"), un = oc.find((o) => o.name === "Under");
          if (ov || un) e.tot = [(ov || un).point, ov?.price ?? null, un?.price ?? null];
        }
      }
      e.book ??= k;
    }
    if (e.ml || e.pl || e.tot) { nhlGameLinesLive[g.id] = { ...e, fetched: new Date().toISOString() }; n++; }
  }
  store.set("nhlBoard.gameLines", nhlGameLinesLive);
  return n;
}
function nhlGameLines(g) {
  const a = nhlGameLinesLive[g.id], b = D.nhl?.gameLines?.[g.id];
  if (a && b) return (a.fetched || "") >= (b.fetched || "") ? a : b;
  return a || b || null;
}
async function loadNhlOdds(key, book) {
  let nLines = 0, linesErr = "";
  try { nLines = await loadNhlGameLines(key, book); } catch (e) { if (/credits/.test(e.message)) throw e; linesErr = " Game lines couldn't load."; }
  const linesMsg = ` Game lines (moneyline, puck line, total) for ${nLines} game${nLines === 1 ? "" : "s"}.${linesErr}`;
  const games = (D.nhl?.games || []).filter((g) => g.day === state.date && !(D.nhl.proj?.[g.id] || []).some((r) => r.res));
  if (!games.length) return nLines ? `NHL:${linesMsg}` : "";
  const events = await oddsEvents(NHL_ODDS_BASE, key);
  const same = (a, b) => { a = normName(a); b = normName(b); return a === b || a.split(" ").pop() === b.split(" ").pop(); };
  let priced = 0, withBook = 0, withSog = 0, firstEv = null;
  const usedBooks = new Set();
  for (const g of games) {
    const ev = events.find((e) => same(e.home_team, D.nhl.teams?.[g.home]?.[0] || g.home) && same(e.away_team, D.nhl.teams?.[g.away]?.[0] || g.away) &&
      new Intl.DateTimeFormat("en-CA", { timeZone: ET }).format(new Date(e.commence_time)) === g.day);
    if (!ev) continue;
    firstEv ??= { ev, g };
    // Ask for every Hard Rock feed in one call (same 1 credit); prefer the selected one, then plain "Hard Rock Bet", then the rest
    const order = [book, "hardrockbet", ...Object.keys(BOOKS)].filter((k, i, a) => a.indexOf(k) === i);
    const r = await fetch(`${NHL_ODDS_BASE}/events/${ev.id}/odds?apiKey=${encodeURIComponent(key)}&bookmakers=${order.join(",")}&markets=player_points,player_shots_on_goal&oddsFormat=american`);
    oddsRemaining = r.headers.get("x-requests-remaining") ?? oddsRemaining;
    if (r.status === 429) throw new Error("Out of Odds API credits for this month");
    if (!r.ok) continue;
    priced++;
    const data = await r.json(), byBook = {};
    for (const bm of data.bookmakers || []) for (const m of bm.markets || []) {
      const stat = NHL_MARKETS[m.key];
      if (!stat) continue;
      const bp = (byBook[bm.key] ??= {});
      for (const o of m.outcomes || []) {
        const pid = nhlPidByName(g, o.description || "");
        if (!pid || o.point == null || !["Over", "Under"].includes(o.name)) continue;
        const L = ((bp[pid] ??= {})[stat] ??= []);
        let sl = L.find((x) => x[0] === o.point);
        if (!sl) { sl = [o.point, null, null]; L.push(sl); }
        sl[o.name === "Over" ? 1 : 2] = Math.round(o.price);
      }
    }
    const props = {};
    for (const k of order) for (const [pid, v] of Object.entries(byBook[k] || {}))
      for (const [st, L] of Object.entries(v)) if (L.length) (props[pid] ??= {})[st] ??= L;
    Object.keys(byBook).forEach((k) => usedBooks.add(k));
    const ps = Object.values(props);
    if (ps.some((v) => v.pts)) withBook++;
    if (ps.some((v) => v.sog)) withSog++;
    nhlLive[g.id] = { book, fetched: new Date().toISOString(), props };
  }
  store.set("nhlBoard.liveOdds", nhlLive);
  let why = "";
  if (!withBook && firstEv) {
    // Hard Rock came back empty: see which US books DO list NHL player points for one game (about 2 credits)
    try {
      const r = await fetch(`${NHL_ODDS_BASE}/events/${firstEv.ev.id}/odds?apiKey=${encodeURIComponent(key)}&regions=us,us2&markets=player_points&oddsFormat=american`);
      oddsRemaining = r.headers.get("x-requests-remaining") ?? oddsRemaining;
      if (r.ok) {
        const d = await r.json();
        const have = (d.bookmakers || []).filter((b) => (b.markets || []).some((m) => m.key === "player_points" && (m.outcomes || []).length)).map((b) => b.title);
        const hr = (d.bookmakers || []).filter((b) => /hard ?rock/i.test(b.title) && (b.markets || []).length).map((b) => b.title);
        const gm = `${firstEv.g.away} @ ${firstEv.g.home}`;
        why = have.length
          ? ` Hard Rock isn't offering NHL player-points props through The Odds API right now${hr.length ? ` (other Hard Rock states: ${hr.join(", ")})` : ""}. For ${gm} they're available from: ${have.join(", ")}.`
          : ` No US sportsbook has posted NHL player-points props for ${gm} through The Odds API yet. They usually appear on game day; try again closer to puck drop.`;
      }
    } catch (e) { /* diagnostic is best-effort */ }
  }
  const src = [...usedBooks].map((k) => BOOKS[k] || k).join(" + ");
  return `NHL: Hard Rock points lines for ${withBook} and shots lines for ${withSog} of ${games.length} game${games.length > 1 ? "s" : ""}${src ? ` (from ${src})` : ""}` +
    (priced > Math.max(withBook, withSog) ? ` (${priced - Math.max(withBook, withSog)} not posted yet).` : ".") + linesMsg + why;
}

async function loadAllOdds() {
  const key = $("apiKey").value.trim();
  if (!key) { oddsMsg = { text: "Paste your Odds API key in settings (the gear) first.", err: true }; render(); return; }
  store.set("nflBoard.oddsApiKey", key);
  const book = currentBook();
  oddsMsg = { text: "Loading Hard Rock odds for NFL and NHL…", err: false }; render();
  const parts = []; let errs = 0;
  for (const [lab, fn] of [["NFL", loadNflOdds], ["NHL", loadNhlOdds]]) {
    try { const m = await fn(key, book); if (m) parts.push(m); }
    catch (e) { errs++; parts.push(`${lab}: ${e instanceof TypeError ? "your browser blocked the request to The Odds API" : e.message}.`); }
  }
  if (!parts.length) parts.push("No upcoming NFL or NHL games on this day to price.");
  if (oddsRemaining != null) parts.push(`${oddsRemaining} credits left this month.`);
  oddsMsg = { text: parts.join(" "), err: errs > 0 && errs === parts.length };
  render();
}

// Odds you type in yourself (kept in this browser only)
const MANUAL_KEY = "nflBoard.manualOdds";
let manualOdds = {};
try { manualOdds = JSON.parse(localStorage.getItem(MANUAL_KEY) || "{}"); } catch (e) { manualOdds = {}; }
function saveManual() { try { localStorage.setItem(MANUAL_KEY, JSON.stringify(manualOdds)); } catch (e) { /* storage unavailable */ } }
const OUT_KEY = "nflBoard.markedOut";
let markedOut = {};
try { markedOut = JSON.parse(localStorage.getItem(OUT_KEY) || "{}"); } catch (e) { markedOut = {}; }
function saveOut() { try { localStorage.setItem(OUT_KEY, JSON.stringify(markedOut)); } catch (e) { /* storage unavailable */ } }
function parseOdds(text) {
  const t = String(text).trim().replace("−", "-");
  if (!t) return null;
  const m = t.match(/^([+-])?(\d{3,5})$/);
  if (!m) return undefined;
  const v = Number(m[2]) * (m[1] === "-" ? -1 : 1);
  return Math.abs(v) >= 100 ? v : undefined;
}
function tdRows(g) {
  const hits = new Set(D.tdHits?.[g.id] || []);
  const base = D.td?.[g.id] || [];
  // Players you mark out: remove them and hand their share of the team's expected TDs to teammates
  const isOut = (r) => !!markedOut[`${g.id}|${r.pid}`];
  const lost = {};
  for (const r of base) if (isOut(r)) {
    const t = (lost[r.team] ??= { rs: 0, cs: 0 });
    t.rs += r.rs; t.cs += r.cs;
  }
  return base.map((r) => {
    const opp = r.team === g.home ? g.away : g.home;
    const out = isOut(r);
    const L = lost[r.team] || { rs: 0, cs: 0 };
    const lr = out ? 0 : r.lr / Math.max(0.05, 1 - L.rs), lc = out ? 0 : r.lc / Math.max(0.05, 1 - L.cs);
    const p = out ? 0 : 1 - Math.exp(-(lr + lc));
    const manual = manualOdds[`${g.id}|${r.pid}`];
    const lf = liveFor(g.id), builtAt = D.oddsTimes?.[g.id];
    const liveNewer = lf && (!builtAt || new Date(lf.fetched) > new Date(builtAt));
    const live = liveNewer ? lf.prices?.[r.pid] : undefined;
    const bookPrice = liveNewer ? (live ?? null) : (r.book ?? null);
    const price = bookPrice ?? manual ?? null;
    return { ...r, lr, lc, p, out, adjusted: !out && (L.rs > 0 || L.cs > 0), game: g, opp, m: g.ctx.dvp[opp]?.[r.pos],
      book: bookPrice, price, manual: bookPrice == null && manual != null,
      scored: g.hs !== null ? hits.has(r.pid) : null, ...(out ? { bookP: null, edge: null, ev: null } : bookMath(p, price)) };
  }).sort((a, b) => (a.out - b.out) || (b.p - a.p));
}
// Sportsbook comparison: implied chance from the price, edge in points, expected profit per $100
function bookMath(p, price) {
  if (price == null) return { bookP: null, edge: null, ev: null };
  const bookP = price > 0 ? 100 / (price + 100) : -price / (-price + 100);
  const profit = price > 0 ? price : 10000 / -price;
  return { bookP, edge: p - bookP, ev: p * profit - (1 - p) * 100 };
}
const fmtOdds = (v) => v == null ? "" : v > 0 ? `+${v}` : `−${Math.abs(v)}`;
const TD_ALLOWED = { QB: (pg) => pg[S.rtd], RB: (pg) => pg[S.rtd] + pg[S.retd], WR: (pg) => pg[S.retd], TE: (pg) => pg[S.retd] };

// Red-zone usage by role: receivers show targets, QBs show carries, running backs show both
function rzText(pos, car, tgt) {
  if (pos === "WR" || pos === "TE") return `${tgt} tgt`;
  if (pos === "QB") return `${car} car`;
  return `${car} car, ${tgt} tgt`;
}
function tdTable(rows, showGame) {
  if (!rows.length) return `<p class="note">No touchdown projections for these games yet.</p>`;
  const body = rows.map((r) => {
    const key0 = `${r.game.id}|${r.pid}`;
    if (r.out) {
      return `<tr class="outrow"><td colspan="4"><div class="pcell">${headshot(r)}<div><span class="pname">${esc(r.name)}</span> <span class="flag">Marked out</span>
        <span class="sub">${matchupText(r)}. Share moved to teammates.</span><button class="mini" data-out="${esc(key0)}">Undo</button></div></div></td></tr>`;
    }
    const flags = (r.miss ? ` <span class="flag">Missed last game</span>` : "") +
      (r.fill ? ` <span class="flag">Fill-in starter</span>` : "") +
      (r.inj ? ` <span class="flag">${esc(r.inj[0])}${r.inj[1] ? ` (${esc(r.inj[1])})` : ""}</span>` : "") +
      (r.adjusted ? ` <span class="flag adj">Up: teammate out</span>` : "");
    const outBtn = r.game.hs === null ? `<button class="mini" data-out="${esc(key0)}" title="Remove this player and give his share to teammates">Mark out</button>` : "";
    const split = [r.lr > 0.005 ? `rush ${Math.round(100 * (1 - Math.exp(-r.lr)))}%` : "", r.lc > 0.005 ? `rec ${Math.round(100 * (1 - Math.exp(-r.lc)))}%` : ""].filter(Boolean).join(", ");
    const better = r.price != null && r.edge > 0;
    const key = `${r.game.id}|${r.pid}`;
    const book = r.book != null
      ? `<b class="${better ? "up" : "down"}">${fmtOdds(r.book)}</b>`
      : `<input class="oin" aria-label="Enter Hard Rock odds for ${esc(r.name)}" placeholder="odds" data-k="${esc(key)}" value="${r.manual ? fmtOdds(r.price).replace("−", "-") : ""}">`;
    const edge = r.price == null ? `<span class="sub">Enter Hard Rock's price to see the edge</span>`
      : `<span class="edgeline ${better ? "up" : "down"}">${better ? "+" : "−"}${Math.abs(r.edge * 100).toFixed(1)}%</span>${r.manual ? `
         <span class="sub">Your price</span>` : ""}`;
    const result = r.scored === null ? "" : `<span class="sub">${r.scored ? `<b class="hit">Scored</b>` : "Didn't score"}</span>`;
    const mx = r.mx != null && Math.abs(r.mx) >= 0.0005 ? ` (${r.mx > 0 ? "+" : "−"}${Math.abs(r.mx * 100).toFixed(1)}%)` : "";
    const ctx = `<div class="why">
      <span>${matchChip(r.m?.rank)} vs ${esc(r.opp)} D${mx}</span>
      <span>Red zone: ${rzText(r.pos, r.rz[0], r.rz[1])}, inside 10: ${rzText(r.pos, r.rz[2], r.rz[3])}</span>
      <span>${r.td} TD this season</span>
      ${r.car && r.car[1] ? `<span>${D.season - 1}: ${r.car[2]} TD in ${r.car[1]} g</span>` : ""}
    </div>`;
    return `<tr${better ? ' class="value"' : ""}>
      <td><div class="pcell">${headshot(r)}<div><span class="pos">${r.pos}</span><span class="pname">${esc(r.name)}</span>${flags}
        <span class="sub">${matchupText(r)}${showGame ? `, ${prettyTime(r.game.time)}` : ""}</span>${outBtn}</div></div></td>
      <td><div class="prob"><b>${Math.round(r.p * 100)}%</b><div class="pbar"><i style="width:${Math.min(100, r.p * 150)}%"></i></div></div>
        <span class="sub">${split}</span>${result}</td>
      <td><div class="pricepair"><span><small>Fair</small><b>${fairOdds(r.p)}</b></span><span><small>Hard Rock</small>${book}</span></div>${edge}</td>
      <td>${ctx}</td>
    </tr>`;
  }).join("");
  return `<div class="tbl"><table class="tdtable"><colgroup><col class="c-player"><col class="c-a"><col class="c-b"><col class="c-c"></colgroup>
    <thead><tr><th>Player</th><th>TD chance</th><th>Price and edge</th><th>Why</th></tr></thead><tbody>${body}</tbody></table></div>`;
}

function injuryNote(g) {
  const list = D.injuries?.[g.id] || [];
  if (!list.length) return "";
  return `<p class="alert"><b>Out or doubtful</b> on the injury report, with their share given to teammates: ${list.map(([n, t, pos, st, inj]) =>
    `${esc(n)} (${esc(t)} ${esc(pos)}, ${esc(st)}${inj ? ", " + esc(inj) : ""})`).join("; ")}.</p>`;
}

// Player photo: a small face crop from the NFL's image server, falling back to the full image, then initials
// Small team logo, shown as a badge on player photos and next to team names
function teamLogo(abbr, cls = "tlogo") {
  const url = D.teams?.[abbr]?.[1];
  return url ? `<img class="${cls}" src="${esc(url)}" alt="${esc(abbr)}" title="${esc(D.teams[abbr][0])}" loading="lazy" onerror="this.remove()">` : "";
}
function matchupText(r) {
  return `<span class="mup">${teamLogo(r.team, "mlogo")}${esc(r.team)} vs ${teamLogo(r.opp, "mlogo")}${esc(r.opp)}</span>`;
}
function headshot(r) {
  return `<span class="hswrap">${photo(r)}${teamLogo(r.team, "hsbadge")}</span>`;
}
function photo(r) {
  const url = D.heads?.[r.pid];
  const initials = esc((r.name || "").split(" ").map((w) => w[0]).filter(Boolean).slice(0, 2).join(""));
  if (!url) return `<span class="hs hs-none" aria-hidden="true">${initials}</span>`;
  const small = url.replace("/upload/f_auto,q_auto/", "/upload/f_auto,q_auto,c_thumb,g_face,w_112,h_112/");
  return `<img class="hs" src="${esc(small)}" alt="" loading="lazy" data-full="${esc(url)}" data-initials="${initials}"
    onerror="if(this.dataset.full && this.src!==this.dataset.full){this.src=this.dataset.full}else{const s=document.createElement('span');s.className='hs hs-none';s.textContent=this.dataset.initials;this.replaceWith(s)}">`;
}

function careerLine(r) {
  if (!r.car) return "";
  const [age, g, td, xtd] = r.car;
  const bits = [];
  if (age) bits.push(`Age ${age}`);
  bits.push(g ? `${D.season - 1}: ${td} TD (${xtd.toFixed(1)} expected) in ${g} g` : `No ${D.season - 1} games`);
  return `<span class="sub">${bits.join(". ")}</span>`;
}

function matchupStrip(g) {
  const line = (def, off) => `<div class="mstrip"><span class="mlabel">${esc(def)} defense vs ${esc(off)}</span>${POSITIONS.map((pos) => {
    const x = g.ctx.dvp[def]?.[pos];
    return `<span class="mpos"><span class="pos">${pos}</span>${matchChip(x?.rank)}<span class="sub">${x ? `${f0(x.val)} ${DVP[pos].label.toLowerCase()}, ${f1(TD_ALLOWED[pos](x.pg))} TD/g` : "no games yet"}</span></span>`;
  }).join("")}</div>`;
  return `<h3 style="margin-top:14px">Position matchup ranks</h3>${line(g.home, g.away)}${line(g.away, g.home)}`;
}

function bookNote() {
  const times = [...Object.values(D.oddsTimes || {}), ...Object.values(liveOdds).filter((x) => x.book === currentBook()).map((x) => x.fetched)];
  if (times.length) {
    const latest = times.sort().pop();
    return `Hard Rock prices last refreshed ${new Date(latest).toLocaleString("en-US", { timeZone: ET, month: "short", day: "numeric", hour: "numeric", minute: "2-digit" })} ET; refresh before betting since lines move. Edge is the model's chance minus the chance the price implies, with the book's margin left in.`;
  }
  const anyLive = Object.values(liveOdds).find((x) => x.book === currentBook());
  if (anyLive) return `${esc(BOOKS[currentBook()])} prices loaded ${new Date(anyLive.fetched).toLocaleString("en-US", { timeZone: ET, month: "short", day: "numeric", hour: "numeric", minute: "2-digit" })} ET; reload before betting since lines move. Edge is the model's chance minus the chance the price implies, with the book's margin left in.`;
  if (!D.book) return `Type the prices from the Hard Rock app into the odds boxes (like +250 or -120) to see the edge; they're saved in this browser. Or rebuild with a free The Odds API key to fill them in automatically.`;
  return `${esc(D.book.name)} prices as of ${esc(D.book.fetched)}; rebuild before betting since lines move. Edge is the model's chance minus the chance the price implies, with the book's margin left in.`;
}

function tdPanel(g) {
  const rows = tdRows(g);
  if (!rows.length) return "";
  const shown = rows.filter((r) => r.p >= 0.05 || r.price != null || r.out);
  const lf = liveFor(g.id), builtAt = D.oddsTimes?.[g.id];
  const extra = (lf && (!builtAt || new Date(lf.fetched) > new Date(builtAt))) ? (lf.extra || []) : (D.bookOnly?.[g.id] || []).map(([n, p]) => [n, p]);
  return `<details class="howto"><summary>How this is calculated</summary><p class="tdctx">Injury report applied; use Mark out for late news. Chance each player scores a rushing or receiving TD, from each team's Vegas-implied points and each player's share of their team's expected touchdowns. Fair odds are the break-even price. ${bookNote()} Matchup rank: 32 means the opponent allows the most to that position (green), 1 the least.</p></details>
    ${tdTable(shown, false)}
    ${injuryNote(g)}
    ${extra.length ? `<p class="tdctx">Also on the board at Hard Rock, no projection from the model: ${extra.map(([n, pr]) => `${esc(n)} ${fmtOdds(pr)}`).join(", ")}.</p>` : ""}
    ${matchupStrip(g)}`;
}

/* ---------- yards, receptions and rush attempts ---------- */
const PROP = {
  rec_yds: { i: 0, label: "Receiving yards", unit: "rec yds", pos: ["RB", "WR", "TE"], share: "t" },
  rec: { i: 1, label: "Receptions", unit: "rec", pos: ["RB", "WR", "TE"], share: "t" },
  rush_yds: { i: 2, label: "Rushing yards", unit: "rush yds", pos: ["QB", "RB"], share: "c" },
  rush_att: { i: 3, label: "Rush attempts", unit: "rush att", pos: ["QB", "RB"], share: "c" },
};
let manualProps = store.get("nflBoard.manualProps", {});
function muBucket(stat, mu) { const c = { rec_yds: [20, 45], rec: [2, 4], rush_yds: [25, 55], rush_att: [6, 13] }[stat]; return mu < c[0] ? 0 : mu < c[1] ? 1 : 2; }
function propQ(stat, mu) { return D.ratioQ?.[`${stat}|${muBucket(stat, mu)}`] || []; }
function pOver(stat, mu, line) {
  const qs = propQ(stat, mu);
  if (!qs.length) return null;
  let c = 0; for (const q of qs) if (mu * q > line) c++;
  return 0.5 + (D.pShrink ?? 0.75) * (c / qs.length - 0.5);
}
function modelMedian(stat, mu) { const qs = propQ(stat, mu); return qs.length ? mu * qs[Math.floor(qs.length / 2)] : mu; }
const implied = (price) => price > 0 ? 100 / (price + 100) : -price / (-price + 100);
const profit = (price) => price > 0 ? price : 10000 / -price;

function propRows(g, stat) {
  const P = PROP[stat], base = (D.props?.[g.id] || []).filter((r) => r.mu[P.i] != null && P.pos.includes(r.pos));
  const all = D.props?.[g.id] || [];
  const lost = {};
  for (const r of all) if (markedOut[`${g.id}|${r.pid}`]) { const t = (lost[r.team] ??= { t: 0, c: 0 }); t.t += r.ts || 0; t.c += r.cs || 0; }
  const lf = liveFor(g.id), builtAt = D.oddsTimes?.[g.id];
  const liveNewer = lf && (!builtAt || new Date(lf.fetched) > new Date(builtAt));
  return base.map((r) => {
    const out = !!markedOut[`${g.id}|${r.pid}`];
    const L = lost[r.team] || { t: 0, c: 0 };
    const scale = P.share === "t" ? 1 / Math.max(0.05, 1 - L.t) : 1 / Math.max(0.05, 1 - L.c);
    const mu = out ? 0 : r.mu[P.i] * scale;
    const opp = r.team === g.home ? g.away : g.home;
    const bookRow = liveNewer ? lf.props?.[stat]?.[r.pid] : D.propOdds?.[g.id]?.[r.pid]?.[stat];
    const man = manualProps[`${g.id}|${r.pid}|${stat}`];
    let line = null, over = null, under = null, src = null;
    if (bookRow) { [line, over, under] = bookRow; src = "book"; }
    else if (man && man.line != null) { ({ line, over, under } = man); src = "manual"; }
    const med = modelMedian(stat, mu);
    const modelLine = Math.floor(med) + 0.5;
    const pO = out ? null : pOver(stat, mu, line ?? modelLine);
    let best = null;
    if (pO != null && line != null) {
      for (const [side, p, price] of [["Over", pO, over], ["Under", 1 - pO, under]]) {
        if (price == null) continue;
        const e = { side, p, price, edge: p - implied(price), ev: p * profit(price) - (1 - p) * 100 };
        if (!best || e.edge > best.edge) best = e;
      }
    }
    const actual = r.act ? r.act[P.i] : null;
    return { ...r, g, stat, opp, out, mu, med, line, over, under, src, modelLine, pO, best, actual,
      adjusted: !out && scale > 1.0001, m: g.ctx.dvp[opp]?.[r.pos] };
  });
}

function oddsInputs(r) {
  const k = `${r.g.id}|${r.pid}|${r.stat}`, man = manualProps[k] || {};
  const inp = (f, ph, v) => `<input class="oin pin" data-pk="${esc(k)}" data-f="${f}" placeholder="${ph}" aria-label="${ph} for ${esc(r.name)}" value="${v == null ? "" : (f === "line" ? v : fmtOdds(v).replace("−", "-"))}">`;
  return `<div class="pinputs">${inp("line", "Line", man.line)}${inp("over", "Over", man.over)}${inp("under", "Under", man.under)}</div>`;
}

function propTable(rows, showGame) {
  if (!rows.length) return `<p class="note">No projections for these games yet.</p>`;
  const P = PROP[rows[0].stat];
  const body = rows.map((r) => {
    const key0 = `${r.g.id}|${r.pid}`;
    if (r.out) return `<tr class="outrow"><td colspan="4"><div class="pcell">${headshot(r)}<div><span class="pname">${esc(r.name)}</span> <span class="flag">Marked out</span>
      <span class="sub">${matchupText(r)}. Volume moved to teammates.</span><button class="mini" data-out="${esc(key0)}">Undo</button></div></div></td></tr>`;
    const flags = (r.inj ? ` <span class="flag">${esc(r.inj[0])}${r.inj[1] ? ` (${esc(r.inj[1])})` : ""}</span>` : "") +
      (r.adjusted ? ` <span class="flag adj">Up: teammate out</span>` : "");
    const usage = P.share === "t"
      ? `${Math.round((r.ts || 0) * 100)}% target share, ${(r.tgt || 0).toFixed(1)} targets projected`
      : `${Math.round((r.cs || 0) * 100)}% of carries, ${(r.car || 0).toFixed(1)} projected`;
    const outBtn = r.g.hs === null ? `<button class="mini" data-out="${esc(key0)}" title="Remove this player and give his volume to teammates">Mark out</button>` : "";
    const avg = r.avg[P.i], l3 = r.l3[P.i];
    const line = r.line ?? r.modelLine;
    const pO = r.pO ?? 0.5, pU = 1 - pO;
    const lineTop = r.src === "book"
      ? `<div class="lineb"><b>${r.line}</b><span>o ${fmtOdds(r.over)}</span><span>u ${fmtOdds(r.under)}</span></div>`
      : `${oddsInputs(r)}<span class="sub">${r.src === "manual" ? "Your line" : `No Hard Rock line yet. Model line ${r.modelLine}`}</span>`;
    const model = `<div class="ou"><span class="${pO >= 0.5 ? "up" : ""}">Over ${Math.round(pO * 100)}% <small>${fairOdds(pO)}</small></span><span class="${pU > 0.5 ? "up" : ""}">Under ${Math.round(pU * 100)}% <small>${fairOdds(pU)}</small></span></div>`;
    const edge = r.best
      ? `<span class="edgeline ${r.best.edge > 0.0005 ? "up" : "down"}">${r.best.side} ${Math.abs(r.best.edge) < 0.0005 ? "even" : `${r.best.edge > 0 ? "+" : "−"}${Math.abs(r.best.edge * 100).toFixed(1)}%`}</span>
         <span class="sub">${fmtOdds(r.best.price)}</span>`
      : `<span class="sub">Add a line and prices to see the edge</span>`;
    const eff = P.share === "t" ? (r.stat === "rec" ? r.oe[1] : r.oe[0]) : (r.stat === "rush_yds" ? r.oe[2] : null);
    const effTxt = eff != null && Math.abs(eff - 1) >= 0.005
      ? ` (${eff > 1 ? "+" : "−"}${Math.round(Math.abs(eff - 1) * 100)}% ${r.stat === "rec" ? "catch rate" : r.stat === "rush_yds" ? "yds/carry" : "yds/target"})` : "";
    const logv = r.log.map((x) => x[P.i]);
    const hits = logv.filter((v) => v > line).length;
    const logTxt = logv.length ? `Last ${logv.length}: ${logv.map((v) => `<b class="${v > line ? "up" : "muted"}">${v}</b>`).join(" ")} (${hits} over)` : "No games this season";
    const result = r.actual == null ? "" : `<span class="sub">Result: <b class="${r.actual > line ? "up" : "down"}">${r.actual}</b>, ${r.actual > line ? "over" : "under"}</span>`;
    return `<tr${r.best && r.best.edge > 0 ? ' class="value"' : ""}>
      <td><div class="pcell">${headshot(r)}<div><span class="pos">${r.pos}</span><span class="pname">${esc(r.name)}</span>${flags}
        <span class="sub">${matchupText(r)}${showGame ? `, ${prettyTime(r.g.time)}` : ""}</span><span class="sub">${usage}</span>${outBtn}</div></div></td>
      <td><b class="big">${r.mu.toFixed(1)}</b><span class="sub">median ${r.med.toFixed(1)}</span>
        <span class="sub">${avg != null ? `avg ${avg}, last 3 ${l3}` : "no games yet"}</span>${result}</td>
      <td>${lineTop}${model}</td>
      <td>${edge}<div class="why"><span>${matchChip(r.m?.rank)} vs ${esc(r.opp)} D${effTxt}</span><span class="logc">${logTxt}</span></div></td>
    </tr>`;
  }).join("");
  return `<div class="tbl"><table class="tdtable"><colgroup><col class="c-player"><col class="c-a"><col class="c-b"><col class="c-c"></colgroup>
    <thead><tr><th>Player</th><th>Projection</th><th>Line and model</th><th>Edge and why</th></tr></thead><tbody>${body}</tbody></table></div>`;
}

function renderPropBoard(board, games) {
  const tab = state.view, stat = tab === "yds" ? state.ydsStat : state.volStat, P = PROP[stat];
  const choices = tab === "yds" ? [["rec_yds", "Receiving yards"], ["rush_yds", "Rushing yards"]] : [["rec", "Receptions"], ["rush_att", "Rush attempts"]];
  let rows = games.flatMap((g) => propRows(g, stat));
  const outRows = rows.filter((r) => r.out);
  rows = rows.filter((r) => !r.out && (state.propPos === "All" || r.pos === state.propPos));
  if (state.propSort === "edge") rows.sort((a, b) => (b.best?.edge ?? -9) - (a.best?.edge ?? -9) || b.mu - a.mu);
  else rows.sort((a, b) => b.mu - a.mu);
  const btns = (items, cur, attr) => `<div class="posf" role="group">${items.map(([k, l]) =>
    `<button ${attr}="${k}" aria-pressed="${cur === k}">${l}</button>`).join("")}</div>`;
  board.innerHTML = `<div class="tdwrap"><div class="tdhead"><h2>${P.label}</h2>
    <div class="controls">${btns(choices, stat, "data-ps")}${btns([["edge", "Sort by edge"], ["proj", "Sort by projection"]], state.propSort, "data-sort")}
    ${btns([["All", "All"], ...P.pos.map((p) => [p, p])], state.propPos, "data-pp")}
    <button id="exportProps">Export CSV</button></div></div>
    <details class="howto"><summary>How this is calculated</summary><p class="tdctx">Projection = the player's expected ${P.unit} tonight: his team's expected ${P.share === "t" ? "targets" : "carries"} (this season plus the last three, adjusted for the point spread, the Vegas total, both teams' pace, this defense and the kickoff forecast for wind and cold) times his share (nudged up or down when his recent snap count changes), times his ${stat === "rec" ? "catch rate" : stat === "rec_yds" ? "yards per target" : stat === "rush_yds" ? "yards per carry" : "carries"}${stat === "rush_att" ? "" : " regressed to his position and adjusted for this defense, missing defensive backs, and his starting quarterback's accuracy"}. Over/under chances use the real game-to-game spread from 2024–25 backtests. Type Hard Rock's line and prices into the boxes, or Refresh with your key to fill them. ${bookNote()}</p></details>
    ${games.map(injuryNote).join("")}
    ${propTable([...rows.slice(0, 80), ...outRows], true)}</div>`;
  board.querySelectorAll("[data-ps]").forEach((b) => b.addEventListener("click", () => { state[tab === "yds" ? "ydsStat" : "volStat"] = b.dataset.ps; state.propPos = "All"; render(); }));
  board.querySelectorAll("[data-sort]").forEach((b) => b.addEventListener("click", () => { state.propSort = b.dataset.sort; render(); }));
  board.querySelectorAll("[data-pp]").forEach((b) => b.addEventListener("click", () => { state.propPos = b.dataset.pp; render(); }));
  $("exportProps").addEventListener("click", () => exportProps(games, stat));
}

function exportProps(games, stat) {
  const P = PROP[stat];
  const rows = [["Date", "Kickoff (ET)", "Player", "Pos", "Team", "Opponent", `Projected ${P.unit}`, "Model median", "Season avg", "Last 3 avg",
    "Line", "Over odds", "Under odds", "Line source", "P(over)", "P(under)", "Fair over", "Fair under", "Best side", "Edge (%)", "EV per $100",
    "Opp D vs pos rank", "Last 6 games", "Result"]];
  for (const r of games.flatMap((g) => propRows(g, stat)).filter((r) => !r.out).sort((a, b) => (b.best?.edge ?? -9) - (a.best?.edge ?? -9))) {
    const line = r.line ?? r.modelLine, pO = r.pO ?? 0.5;
    rows.push([r.g.day, prettyTime(r.g.time), r.name, r.pos, r.team, r.opp, r.mu.toFixed(1), r.med.toFixed(1), r.avg[P.i] ?? "", r.l3[P.i] ?? "",
      line, r.over != null ? fmtOdds(r.over) : "", r.under != null ? fmtOdds(r.under) : "", r.src || "model line",
      (pO * 100).toFixed(1) + "%", ((1 - pO) * 100).toFixed(1) + "%", fairOdds(pO), fairOdds(1 - pO),
      r.best?.side ?? "", r.best ? (r.best.edge * 100).toFixed(1) : "", r.best ? r.best.ev.toFixed(0) : "",
      r.m?.rank ?? "", r.log.map((x) => x[P.i]).join(" "), r.actual ?? ""]);
  }
  download(`nfl_${stat}_${state.date}.csv`, rows);
}


function renderTDBoard(board, games) {
  let rows = games.flatMap(tdRows);
  const outRows = rows.filter((r) => r.out);
  rows = rows.filter((r) => !r.out);
  if (state.tdPos !== "All") rows = rows.filter((r) => r.pos === state.tdPos);
  if (state.tdSort === "edge") rows = rows.filter((r) => r.edge != null).sort((a, b) => b.edge - a.edge);
  else rows.sort((a, b) => b.p - a.p);
  const noPrices = state.tdSort === "edge" && !rows.length;
  const sortBtns = true ? `<div class="posf" role="group" aria-label="Sort">${[["chance", "Sort by TD chance"], ["edge", "Sort by edge"]].map(([k, l]) =>
    `<button data-s="${k}" aria-pressed="${state.tdSort === k}">${l}</button>`).join("")}</div>` : "";
  board.innerHTML = `<div class="tdwrap"><div class="tdhead"><h2>Touchdown board</h2>
    <div class="controls">${sortBtns}<div class="posf" role="group" aria-label="Position">${["All", "QB", "RB", "WR", "TE"].map((p) =>
      `<button data-p="${p}" aria-pressed="${state.tdPos === p}">${p}</button>`).join("")}</div></div></div>
    <details class="howto"><summary>How this is calculated</summary><p class="tdctx">Every projected scorer in the selected games. Players listed Out or Doubtful on the official injury report, or who missed their team's last two games, are left out and their share goes to teammates. News after the report (like a surprise inactive) isn't included: use Mark out, and teammates' chances update. ${bookNote()} The model blends this season with the last three (older seasons count less), adjusts older usage for each player's age curve, and values chances by field position so lucky or unlucky TD streaks regress. In backtests on 2024 and 2025, these probabilities beat position-average baselines by about 8% (Brier score) and were well calibrated from 5% to 50%; picks above 50% ran a few points hot, so treat small edges as noise.</p></details>
    ${games.map(injuryNote).join("")}
    ${noPrices ? `<p class="note">No odds for these games yet. Switch to Sort by TD chance and type Hard Rock's prices into the odds boxes, or rebuild with an Odds API key.</p>` : tdTable([...rows.slice(0, 60), ...outRows], true)}</div>`;
  board.querySelectorAll("[data-p]").forEach((b) => b.addEventListener("click", () => { state.tdPos = b.dataset.p; render(); }));
  board.querySelectorAll("[data-s]").forEach((b) => b.addEventListener("click", () => { state.tdSort = b.dataset.s; render(); }));
}

function wireOddsInputs() {
  document.querySelectorAll("input.pin").forEach((el) => {
    el.addEventListener("change", () => {
      const k = el.dataset.pk, f = el.dataset.f, cur = { ...(manualProps[k] || {}) };
      const t = el.value.trim();
      let v = null;
      if (t) {
        v = f === "line" ? Number(t) : parseOdds(t);
        if (v === undefined || Number.isNaN(v) || (f === "line" && v < 0)) {
          el.setCustomValidity(f === "line" ? "Enter a line like 64.5" : "Use American odds like -115 or +105"); el.reportValidity(); return;
        }
      }
      el.setCustomValidity("");
      cur[f] = v;
      if (cur.line == null && cur.over == null && cur.under == null) delete manualProps[k]; else manualProps[k] = cur;
      store.set("nflBoard.manualProps", manualProps); render();
    });
    el.addEventListener("keydown", (e) => { if (e.key === "Enter") el.blur(); });
  });
  document.querySelectorAll("button[data-out]").forEach((el) => el.addEventListener("click", () => {
    const k = el.dataset.out;
    if (markedOut[k]) delete markedOut[k]; else markedOut[k] = true;
    saveOut(); render();
  }));
  document.querySelectorAll("input.oin").forEach((el) => {
    el.addEventListener("change", () => {
      const v = parseOdds(el.value);
      if (v === undefined) { el.setCustomValidity("Use American odds like +250 or -120"); el.reportValidity(); return; }
      el.setCustomValidity("");
      if (v === null) delete manualOdds[el.dataset.k]; else manualOdds[el.dataset.k] = v;
      saveManual(); render();
    });
    el.addEventListener("keydown", (e) => { if (e.key === "Enter") el.blur(); });
  });
}

function render() {
  const msg = $("oddsMsg");
  if (msg) { msg.textContent = oddsMsg.text; msg.className = "oddsmsg" + (oddsMsg.err ? " err" : "") + (oddsMsg.text ? " on" : ""); }
  renderInner();
  wireOddsInputs();
}
function renderInner() {
  { const [y, m, d] = state.date.split("-").map(Number);
    const dt = new Date(Date.UTC(y, m - 1, d, 12));
    const long = dt.toLocaleDateString("en-US", { timeZone: "UTC", weekday: "long", month: "long", day: "numeric" });
    const short = dt.toLocaleDateString("en-US", { timeZone: "UTC", weekday: "short", month: "short", day: "numeric" });
    $("dateline").innerHTML = `<span class="dl-long">${long}</span><span class="dl-short">${short}</span>`;
    $("dateline").title = prettyDate(state.date); }
  $("date").value = state.date;
  $("expand").textContent = state.openAll ? "Close all player views" : "Open all TD outlooks";
  document.querySelectorAll(".windows button").forEach((b) => b.setAttribute("aria-pressed", String(b.dataset.w === state.windowKey)));
  document.querySelectorAll(".views button").forEach((b) => b.setAttribute("aria-pressed", String(b.dataset.v === state.view)));
  $("expand").style.display = state.view === "games" ? "" : "none";
  $("export").style.display = $("exportPlayers").style.display = state.view === "games" ? "" : "none";
  $("exportTD").style.display = state.view === "td" ? "" : "none";
  document.body.dataset.sport = state.sport;
  document.querySelectorAll(".sport button").forEach((b) => b.setAttribute("aria-pressed", String(b.dataset.sport === state.sport)));
  if (state.sport === "nhl") { renderNHL($("board")); return; }
  const dayGames = gamesOn(state.date);
  if (dayGames.length) {
    const times = dayGames.map((g) => g.time).sort();
    const span = times[0] === times[times.length - 1] ? prettyTime(times[0]) : `${prettyTime(times[0])} to ${prettyTime(times[times.length - 1])}`;
    const done = dayGames.filter((g) => g.hs !== null).length;
    $("slate").textContent = `${dayGames.length} game${dayGames.length > 1 ? "s" : ""}, ${span} ET` + (done === dayGames.length ? ", all final" : done ? `, ${done} final` : "");
  } else $("slate").textContent = "No games";

  $("note").textContent = `Team ranks are points per game; 1 is best. Matchup ranks show how much a defense allows to each position per game: 32 allows the most (green, softest matchup) and 1 allows the least (red, toughest). Everything counts only ${D.season} regular-season games played before the selected date. ` +
    (D.hasPlayerStats ? "" : "No player stats are published for this season yet. ") +
    `Data from nflverse, built ${D.generated}. Click Refresh for the latest. Injury reports come from the official weekly NFL reports; late scratches aren't included, so use Mark out on the Touchdown outlook when news breaks.`;
  const board = $("board"), games = visibleGames();
  if (!games.length) {
    const any = gamesOn(state.date).length > 0, next = nextGameDay(state.date);
    board.innerHTML = `<div class="empty"><h2>No games ${any ? "in this kickoff window" : "on this date"}</h2>
      <p>${any ? "Switch to All day to see every game." : next ? `The next games are on ${prettyDate(next)}.` : `No more ${D.season} games are scheduled. Run nfl_board.py with a newer season.`}</p>
      ${!any && next ? `<button class="primary" id="emptyNext">Show ${esc(prettyDate(next))}</button>` : ""}</div>`;
    $("emptyNext")?.addEventListener("click", () => go(next));
    return;
  }
  if (state.view === "td") { renderTDBoard(board, games); return; }
  if (state.view === "yds" || state.view === "vol") { renderPropBoard(board, games); return; }
  const slots = new Map();
  for (const g of games) { if (!slots.has(g.time)) slots.set(g.time, []); slots.get(g.time).push(g); }
  board.innerHTML = [...slots].map(([t, gs]) => `<section class="slot"><h2>${prettyTime(t)} ET <span>${gs.length} game${gs.length > 1 ? "s" : ""}</span></h2>
    <div class="grid">${gs.map(gameCard).join("")}</div></section>`).join("");
}

/* ---------- CSV exports ---------- */
function download(name, rows) {
  const csv = "\ufeff" + rows.map((r) => r.map((v) => /[",\n]/.test(String(v)) ? `"${String(v).replace(/"/g, '""')}"` : v).join(",")).join("\n");
  const url = URL.createObjectURL(new Blob([csv], { type: "text/csv;charset=utf-8" }));
  const a = Object.assign(document.createElement("a"), { href: url, download: name });
  document.body.append(a); a.click(); a.remove(); URL.revokeObjectURL(url);
}
function exportGames() {
  const head = ["Kickoff (ET)", "Away Team", "Away Off Rank", "Away Def Rank", "Home Team", "Home Off Rank", "Home Def Rank", "Spread (home)", "Total",
    ...["Away", "Home"].flatMap((s) => POSITIONS.map((p) => `${s} D vs ${p} rank`))];
  const rows = visibleGames().map((g) => [`${g.day} ${prettyTime(g.time)}`, g.A.name, g.A.rank.off ?? "", g.A.rank.def ?? "",
    g.H.name, g.H.rank.off ?? "", g.H.rank.def ?? "", g.spread == null ? "" : -g.spread, g.total ?? "",
    ...[g.away, g.home].flatMap((t) => POSITIONS.map((p) => g.ctx.dvp[t]?.[p]?.rank ?? ""))]);
  download(`nfl_tonight_${state.date}.csv`, [head, ...rows]);
}
function exportPlayers() {
  const rows = [["Date", "Team", "Opponent", "Player", "Pos", "Stat", "Season avg", "Last 3 avg", "Games", "Opp D vs pos rank", "Opp allows per game", "Missed last game", "TD chance", "TD fair odds"]];
  for (const g of visibleGames()) {
    for (const [o, d] of [[g.away, g.home], [g.home, g.away]]) {
      const tdBy = Object.fromEntries((D.td?.[g.id] || []).map((r) => [r.pid, r.p]));
      for (const p of keyPlayers(g.ctx, o)) {
        const [label, i] = MAIN[p.pos], m = g.ctx.dvp[d]?.[p.pos], tp = tdBy[p.id];
        rows.push([g.day, o, d, p.name, p.pos, label, f1(p.avg[i]), f1(p.l3[i]), p.n, m?.rank ?? "", m ? f1(m.val) : "", p.missedLast ? "Yes" : "",
          tp != null ? `${Math.round(tp * 100)}%` : "", tp != null ? fairOdds(tp) : ""]);
      }
    }
  }
  download(`nfl_players_${state.date}.csv`, rows);
}

function exportTD() {
  const rows = [["Date", "Kickoff (ET)", "Player", "Pos", "Team", "Opponent", "TD chance", "Fair odds", "Rush share of team xTD", "Rec share of team xTD",
    "RZ carries", "RZ targets", "Inside-10 carries", "Inside-10 targets", "TDs", "Expected TDs", "Team expected TDs", "Team implied pts", "Missed last game", "Result",
    "Book odds", "Book implied", "Edge (%)", "EV per $100", "Opp D vs pos rank", "Opp TD allowed to pos per game",
    "Age", "Last season games", "Last season TDs", "Last season expected TDs", "Age trend"]];
  for (const r of visibleGames().flatMap(tdRows).sort((a, b) => b.p - a.p)) {
    rows.push([r.game.day, prettyTime(r.game.time), r.name, r.pos, r.team, r.opp, (r.p * 100).toFixed(1) + "%", fairOdds(r.p),
      Math.round(r.rs * 100) + "%", Math.round(r.cs * 100) + "%", ...r.rz, r.td, r.xtd, r.tt, r.imp ?? "", r.miss ? "Yes" : "",
      r.scored === null ? "" : r.scored ? "Scored" : "No",
      r.price != null ? fmtOdds(r.price) + (r.manual ? " (entered)" : "") : "", r.bookP != null ? (r.bookP * 100).toFixed(1) + "%" : "",
      r.edge != null ? (r.edge * 100).toFixed(1) : "", r.ev != null ? r.ev.toFixed(0) : "",
      r.m?.rank ?? "", r.m ? TD_ALLOWED[r.pos](r.m.pg).toFixed(2) : "",
      ...(r.car ? [r.car[0] ?? "", r.car[1], r.car[2], r.car[3], `${Math.round((r.car[4] - 1) * 100)}%`] : ["", "", "", "", ""])]);
  }
  download(`nfl_td_board_${state.date}.csv`, rows);
}


/* ================= NHL: player points ================= */
const ND = D.nhl || null;
const NHL_MAN = "nhlBoard.manual", NHL_OUT = "nhlBoard.out";
let nhlManual = store.get(NHL_MAN, {}), nhlOut = store.get(NHL_OUT, {});
Object.assign(state, { nhlLayout: store.get("nhlBoard.layout", "cards"), sport: store.get("board.sport", "nhl"), nhlLine: 0.5, nhlPos: "All", nhlSort: "edge", nhlGame: "all", nhlHide: true,
  lastView: store.get("board.lastView", { nfl: "games", nhl: "nhl_pts" }) });
if (!["nfl", "nhl"].includes(state.sport)) state.sport = "nhl";
if (!["nhl_pts", "nhl_sog", "nhl_games"].includes(state.lastView.nhl)) state.lastView.nhl = "nhl_games";
state.view = state.lastView[state.sport] || (state.sport === "nhl" ? "nhl_pts" : "games");

function nhlGamesOn(ymd) { return (ND?.games || []).filter((g) => g.day === ymd); }
function nhlNextDay(from) { return (ND?.games || []).map((g) => g.day).find((d) => d > from); }
function poisOver(lam, line) {
  let cdf = 0, term = Math.exp(-lam);
  for (let i = 0; i <= Math.floor(line); i++) { if (i) term *= lam / i; cdf += term; }
  return Math.min(1, Math.max(0, 1 - cdf));
}
const impl = (o) => o == null ? null : o > 0 ? 100 / (o + 100) : -o / (-o + 100);
const pct = (p) => `${Math.round(p * 100)}%`;
const NPOS = (p) => p === "D" ? "D" : "F";
function nTeam(abbr) { const t = ND?.teams?.[abbr]; return { name: t?.[0] || abbr, logo: t?.[1] || "" }; }
function nLogo(abbr, cls) { const t = nTeam(abbr); return t.logo ? `<img class="${cls}" src="${esc(t.logo)}" alt="${esc(abbr)}" title="${esc(t.name)}" loading="lazy" onerror="this.remove()">` : ""; }
function nPhoto(r) {
  const ini = esc(r.name.split(" ").map((w) => w[0]).slice(0, 2).join(""));
  const img = r.hs ? `<img class="hs" src="${esc(r.hs)}" alt="" loading="lazy" data-initials="${ini}" onerror="const s=document.createElement('span');s.className='hs hs-none';s.textContent=this.dataset.initials;this.replaceWith(s)">`
    : `<span class="hs hs-none" aria-hidden="true">${ini}</span>`;
  return `<span class="hswrap">${img}${nLogo(r.team, "hsbadge")}</span>`;
}
function likelyOut(r) {
  if (r.lu) return r.lu.status === "out" || r.lu.status === "scratch";
  return r.dressed && r.dressed[1] >= 3 && r.dressed[0] === 0;
}
function luChips(r) {
  const lu = r.lu; if (!lu) return "";
  const c = [];
  if (lu.status === "out") c.push(`<span class="warnpill">Out (injury)</span>`);
  else if (lu.status === "scratch") c.push(`<span class="warnpill">Not in lineup</span>`);
  else {
    if (lu.line) c.push(`<span class="lupill">${r.pos === "D" ? "Pair" : "Line"} ${lu.line}${lu.pp ? ` · PP${lu.pp}` : ""}</span>`);
    if (lu.status === "dtd") c.push(`<span class="warnpill">Day-to-day</span>`);
    if (lu.gtd) c.push(`<span class="warnpill">Game-time decision</span>`);
  }
  return c.join("");
}

function nhlBookLines(g, pid, stat = "pts") {
  const live = nhlLive[g.id];
  let L = (live && live.book === currentBook() ? live.props?.[pid]?.[stat] : null) || D.nhl?.odds?.[g.id]?.[pid]?.[stat] || null;
  if (L && typeof L[0] === "number") L = [L];
  return (L || []).filter((x) => x[1] != null || x[2] != null).sort((a, b) => a[0] - b[0]);
}
function mainLine(L) {
  // Hard Rock's main points line: the one priced closest to even money (both sides posted preferred)
  const both = L.filter((x) => x[1] != null && x[2] != null), pool = both.length ? both : L;
  const dist = (x) => Math.abs((x[1] != null ? impl(x[1]) : 1 - impl(x[2])) - 0.5);
  return pool.reduce((best, x) => (best == null || dist(x) < dist(best) ? x : best), null);
}
function nhlRows(games, stat) {
  const out = [];
  for (const g of games) {
    for (const r of ND.proj?.[g.id] || []) {
      const key = `${g.id}|${r.pid}`, mk = `${key}|${stat}`;
      const lam = r[stat] ?? 0;
      const L = nhlBookLines(g, r.pid, stat), main = L.length ? mainLine(L) : null, mine = nhlManual[mk];
      // no Hard Rock line yet: points default to 0.5; shots to the half-line just under what he's expected to take
      let over = null, under = null, manual = false, line = stat === "sog" ? Math.max(0.5, Math.floor(lam) + 0.5) : 0.5;
      if (main) { [line, over, under] = main; }
      else if (mine && typeof mine === "object") { line = mine.line; over = mine.price; manual = true; }
      const p = poisOver(lam, line);
      const alts = main ? L.filter((x) => x !== main) : [];
      const o = bookMath(p, over), u = bookMath(1 - p, under);
      const noVig = over != null && under != null ? impl(over) / (impl(over) + impl(under)) : null;
      const pickUnder = u.ev != null && (o.ev == null || u.ev > o.ev);
      const best = pickUnder ? { side: "Under", ...u, price: under } : { side: "Over", ...o, price: over };
      const res = r.res ? r.res[stat] : null;
      out.push({ ...r, g, key, mk, stat, lam, p, line, alts, hasBook: !!main, over, under, manual, noVig, best, out: !!nhlOut[key], lik: likelyOut(r),
        hit: res == null ? null : res > line, resv: res });
    }
  }
  return out;
}

function renderNHL(board) {
  if (state.view === "nhl_games") return renderNHLGames(board);
  const stat = state.view === "nhl_sog" ? "sog" : "pts";
  const label = NHL_STAT[stat].label;
  const dayGames = nhlGamesOn(state.date);
  $("slate").textContent = dayGames.length
    ? `${dayGames.length} NHL game${dayGames.length > 1 ? "s" : ""}, ${prettyTime(dayGames.map((g) => g.time).sort()[0])} ET first puck drop`
    : "No NHL games";
  $("note").textContent = stat === "sog"
    ? `Expected shots on goal = his shot attempts per 60 (shots on goal + missed + blocked, which is steadier than shots alone; blended toward what players with his even-strength ice time take) × the share of his attempts that reach the net × projected minutes, where a power-play minute counts about 3 even-strength minutes (shots come much faster on the power play), × how many shots the opponent allows × a little for how much his own team shoots × a small home edge, × 0.95 on the second night of a back-to-back, × a linemate factor (tonight's DailyFaceoff linemates' scoring rate vs his usual linemates, softened), × a rink factor (some arenas' scorers record more or fewer shots; his past shots are de-biased the same way), with power-play minutes scaled by how often the opponent takes penalties. Rookies (flagged on their cards): with few NHL games, minutes lean on tonight's DailyFaceoff line slot and the shot rate starts from players in similar roles (20% lower for rookies outside top-6/PP1 roles, fading as they play), so treat their edges with extra caution. Projected minutes follow his recent ice time, nudged toward tonight's DailyFaceoff line and power-play unit. Chance of going over uses a Poisson curve. Backtested walk-forward on the second half of 2025-26: log-loss 0.438 across the 1.5, 2.5 and 3.5 lines vs 0.509 for a league-average guess, and well calibrated. Edge compares the model to Hard Rock's price (vig included). Data from the NHL API and DailyFaceoff, built ${ND?.generated || "—"}.`
    : `Expected points = even-strength points per 60 (blended toward what players with his ice time produce) × projected even-strength minutes, plus power-play points per 60 × projected power-play minutes, × how many goals the opponent allows × a small home edge. Once Hard Rock posts the game's moneyline and total, projections are also nudged halfway toward the team goals those lines imply (capped at 15%). Even-strength scoring is nudged by tonight's linemates (their scoring rate vs his usual linemates, softened), and power-play minutes by how often the opponent takes penalties. Projected minutes start from his recent ice time and are nudged toward what tonight's DailyFaceoff line and power-play unit usually get (partial weight, since projected lines change). Chance of going over uses a Poisson curve. Backtested walk-forward on every 2025-26 regular-season game and well calibrated for the 0.5 and 1.5 lines. Rookies (flagged on their cards): with few NHL games, projected minutes lean on tonight's DailyFaceoff line slot and the scoring rate starts from players in similar roles, a bit lower for rookies outside top-6/PP1 roles, so their edges are less certain. Players DailyFaceoff lists as injured or leaves out of the lineup are hidden by default; lines marked "projected" can still change at morning skate. Edge compares the model to Hard Rock's price (vig included); the pick shows whichever side, Over or Under, is better. Data from the NHL API and DailyFaceoff, built ${ND?.generated || "—"}.`;
  if (!ND || ND.error) {
    board.innerHTML = `<div class="error"><h2>NHL data isn't loaded</h2><p>${ND?.error ? `The last refresh hit a problem: ${esc(ND.error)}` : "Put nhl_props.py next to nfl_board.py, then click Refresh (or restart Start NFL Board)."}</p></div>`;
    return;
  }
  if (!dayGames.length) {
    const next = nhlNextDay(state.date);
    board.innerHTML = `<div class="empty"><h2>No NHL games on this date</h2><p>${next ? `Next NHL games: ${prettyDate(next)}.` : "No NHL games loaded for the coming week. Click Refresh."}</p>
      ${next ? `<button class="primary" id="emptyNext">Show ${esc(prettyDate(next))}</button>` : ""}</div>`;
    $("emptyNext")?.addEventListener("click", () => go(next));
    return;
  }
  if (state.nhlGame !== "all" && !dayGames.some((g) => g.id === state.nhlGame)) state.nhlGame = "all";
  const games = state.nhlGame === "all" ? dayGames : dayGames.filter((g) => g.id === state.nhlGame);
  let rows = nhlRows(games, stat);
  const all = rows;
  if (state.nhlPos !== "All") rows = rows.filter((r) => NPOS(r.pos) === state.nhlPos);
  if (state.nhlHide) rows = rows.filter((r) => !r.lik || r.res);
  const live = rows.filter((r) => !r.out), outRows = rows.filter((r) => r.out);
  const byChance = stat === "sog" ? (a, b) => b.lam - a.lam : (a, b) => b.p - a.p;
  const byEdge = (a, b) => (b.best.ev ?? -1e9) - (a.best.ev ?? -1e9) || byChance(a, b);
  live.sort(state.nhlSort === "edge" ? byEdge : byChance);
  rows = [...live, ...outRows];
  const shown = rows.slice(0, 160);

  const priced = all.filter((r) => r.best.price != null && !r.out);
  const value = priced.filter((r) => r.best.edge >= 0.03).sort(byEdge);
  const top = all.filter((r) => !r.out && !(state.nhlHide && r.lik)).sort(stat === "sog" ? (a, b) => b.lam - a.lam : (a, b) => b.p - a.p)[0];
  const pill = (attr, k, l, cur) => `<button ${attr}="${k}" aria-pressed="${cur === k}">${l}</button>`;

  board.innerHTML = `<div class="tdwrap">
    <div class="tdhead"><h2>${label}</h2>
      <div class="controls"><button id="nhlExport">Export CSV</button></div></div>
    <div class="nhlsum">
      <div class="stat glass"><small>Games</small><b>${dayGames.length}</b></div>
      <div class="stat glass"><small>Priced props</small><b>${priced.length}</b></div>
      <div class="stat glass"><small>Value plays (3%+ edge)</small><b class="${value.length ? "up" : ""}">${value.length}</b></div>
      <div class="stat glass"><small>${stat === "sog" ? "Most shots expected" : "Most likely"}</small><b style="font-size:1.1rem">${top ? `${esc(top.name)} ${stat === "sog" ? top.lam.toFixed(1) : pct(top.p)}` : "—"}</b></div>
    </div>
    <div class="gamepills" role="group" aria-label="Game">
      <button class="gpill" data-ng="all" aria-pressed="${state.nhlGame === "all"}" style="grid-template-columns:auto">All games<small>${dayGames.length} today</small></button>
      ${dayGames.map((g) => `<button class="gpill" data-ng="${g.id}" aria-pressed="${state.nhlGame === g.id}">${nLogo(g.away, "")}<span>${g.away} @ ${g.home}</span>${nLogo(g.home, "")}
        <small>${g.hs != null && g.state !== "FUT" && g.state !== "PRE" ? `Final ${g.as}–${g.hs}` : prettyTime(g.time) + linesTag(g)}</small></button>`).join("")}
    </div>
    <div class="nhlbar">
      <span class="lbl">Position</span><div class="posf">${["All", "F", "D"].map((p) => pill("data-np", p, p === "F" ? "Forwards" : p === "D" ? "Defense" : "All", state.nhlPos)).join("")}</div>
      <span class="lbl">Sort</span><div class="posf">${pill("data-ns", "edge", "Best edge", state.nhlSort)}${pill("data-ns", "chance", stat === "sog" ? "Most shots" : "Chance", state.nhlSort)}</div>
      <span class="lbl">View</span><div class="posf">${pill("data-nv", "cards", "Cards", state.nhlLayout)}${pill("data-nv", "table", "Table", state.nhlLayout)}</div>
      <label class="toggle"><input type="checkbox" id="nhlHide" ${state.nhlHide ? "checked" : ""}> Hide players out or not in lineup</label>
    </div>
    ${value.length && state.nhlLayout !== "cards" ? `<section class="edges"><h2>Best edges</h2><div class="ticketrow">${value.slice(0, 6).map((r) => `
      <button class="ticket" data-jump="${esc(r.key)}">${nPhoto(r)}<div class="who">${esc(r.name)}<small>${r.team}</small></div>
        <div class="bet">${r.best.side} ${r.line} ${NHL_STAT[stat].unit === "pts" ? "points" : "shots"} · ${fmtOdds(r.best.price)}</div>
        <div class="val"><b>+${(r.best.edge * 100).toFixed(1)}%</b><span>edge</span></div></button>`).join("")}</div></section>` : ""}
    ${state.nhlLayout === "cards"
      ? `<div class="pgrid">${shown.map((r) => nhlCard(r)).join("")}</div>`
      : `<div class="tbl"><table class="tdtable"><colgroup><col class="c-player"><col class="c-a"><col class="c-b"><col class="c-c"></colgroup>
      <thead><tr><th>Player</th><th>Model</th><th>Hard Rock</th><th>Edge</th></tr></thead>
      <tbody>${shown.map((r) => nhlRow(r, stat)).join("")}</tbody></table></div>`}
    ${rows.length > shown.length ? `<p class="note">Showing the top ${shown.length} of ${rows.length}. Pick a game above to see everyone.</p>` : ""}
  </div>`;

  board.querySelectorAll("[data-ng]").forEach((b) => b.addEventListener("click", () => { state.nhlGame = b.dataset.ng; render(); }));
  board.querySelectorAll("[data-np]").forEach((b) => b.addEventListener("click", () => { state.nhlPos = b.dataset.np; render(); }));
  board.querySelectorAll("[data-ns]").forEach((b) => b.addEventListener("click", () => { state.nhlSort = b.dataset.ns; render(); }));
  board.querySelectorAll("[data-nv]").forEach((b) => b.addEventListener("click", () => { state.nhlLayout = b.dataset.nv; store.set("nhlBoard.layout", state.nhlLayout); render(); }));
  $("nhlHide").addEventListener("change", (e) => { state.nhlHide = e.target.checked; render(); });
  $("nhlExport").addEventListener("click", () => nhlExport(all, stat));
  board.querySelectorAll("[data-jump]").forEach((b) => b.addEventListener("click", () =>
    document.querySelector(`[data-row="${CSS.escape(b.dataset.jump)}"]`)?.scrollIntoView({ behavior: "smooth", block: "center" })));
  board.querySelectorAll("button[data-nout]").forEach((b) => b.addEventListener("click", () => {
    const k = b.dataset.nout; if (nhlOut[k]) delete nhlOut[k]; else nhlOut[k] = 1; store.set(NHL_OUT, nhlOut); render(); }));
  board.querySelectorAll("input[data-nm]").forEach((el) => {
    el.addEventListener("change", () => {
      const v = parseOdds(el.value);
      if (v === undefined) { el.style.borderColor = "var(--bad)"; return; }
      const sel = board.querySelector(`select[data-nml="${CSS.escape(el.dataset.nm)}"]`);
      if (v === null) delete nhlManual[el.dataset.nm]; else nhlManual[el.dataset.nm] = { line: Number(sel?.value || 0.5), price: v };
      store.set(NHL_MAN, nhlManual); render();
    });
    el.addEventListener("keydown", (e) => { if (e.key === "Enter") el.blur(); });
  });
  board.querySelectorAll("select[data-nml]").forEach((el) => el.addEventListener("change", () => {
    const m = nhlManual[el.dataset.nml];
    if (m && typeof m === "object") { m.line = Number(el.value); store.set(NHL_MAN, nhlManual); }
    render();
  }));
}

/* ---------- NHL Games: records, team ranks, starting goalies ---------- */
const ord2 = (n) => { const s = ["th", "st", "nd", "rd"], v = n % 100; return n + (s[(v - 20) % 10] || s[v] || s[0]); };
function rankPill(label, rank, val, unit) {
  if (!rank) return "";
  const h = Math.round(135 * (1 - (rank - 1) / 31));
  return `<div class="rk" style="--h:${h}"><small>${label}</small><b>${ord2(rank)}</b><em>${val.toFixed(2)} ${unit}</em></div>`;
}
function goalieRow(gl) {
  if (!gl) return `<div class="ng-goalie none"><span class="gmask" aria-hidden="true"></span><span class="muted">Starter not posted yet</span></div>`;
  const st = (gl.status || "").toLowerCase();
  const cls = st.includes("confirm") ? "conf" : st.includes("likely") ? "likely" : "proj";
  const label = cls === "conf" ? "Confirmed" : cls === "likely" ? "Likely" : "Projected";
  const s = gl.cur && gl.cur.gp ? { ...gl.cur, tag: "" } : gl.last && gl.last.gp ? { ...gl.last, tag: " (last season)" } : null;
  const stats = s ? `${s.sv != null ? s.sv.toFixed(3).replace(/^0/, "") : "—"} SV% · ${s.gaa != null ? s.gaa.toFixed(2) : "—"} GAA · ${s.w}-${s.l}-${s.otl}${s.tag}` : "No NHL stats yet";
  const ini = esc(gl.name.split(" ").map((w) => w[0]).slice(0, 2).join(""));
  const face = gl.hs ? `<span class="gface"><img src="${esc(gl.hs)}" alt="" loading="lazy" data-i="${ini}" onerror="this.parentNode.textContent=this.dataset.i"></span>`
    : `<span class="gface">${ini}</span>`;
  return `<div class="ng-goalie">${face}<div class="gwho"><b>${esc(gl.name)}</b><small>${stats}</small></div>
    <span class="gstat ${cls}" title="${esc(gl.src ? `Source: ${gl.src}` : "")}">${label}</span></div>`;
}
function nhlGameCard(g) {
  const TS = ND.teamStats || {}, GL = (ND.goalies || {})[g.id] || {};
  const final = g.hs != null && g.state !== "FUT" && g.state !== "PRE";
  const live = g.state === "LIVE" || g.state === "CRIT";
  const win = final ? (g.hs > g.as ? g.home : g.away) : null;
  const team = (abbr, score) => {
    const t = TS[abbr], nm = nTeam(abbr).name;
    const rec = t ? `${t.w}-${t.l}-${t.otl} · ${t.pts} pts${t.gp ? ` · L10 ${t.l10.join("-")}${t.streak ? ` · ${t.streak}` : ""}` : ""}` : "";
    const lastRec = t && !t.gp && t.last ? `Last season ${t.last.w}-${t.last.l}-${t.last.otl}, ${t.last.pts} pts` : "";
    return `<div class="ng-team ${win && win !== abbr ? "lost" : ""}">
      ${nLogo(abbr, "ng-logo")}
      <div class="ng-name"><b>${esc(nm)}</b><small>${esc(rec)}${lastRec ? `<br>${esc(lastRec)}` : ""}</small></div>
      <div class="ng-ranks">${t ? rankPill("Offense", t.offRank, t.gfpg, "GF/G") + rankPill("Defense", t.defRank, t.gapg, "GA/G") : ""}</div>
      ${final || live ? `<div class="ng-score">${score ?? ""}</div>` : ""}
    </div>${goalieRow(GL[abbr])}`;
  };
  const status = final ? "Final" : live ? "Live" : `${prettyTime(g.time)} ET`;
  return `<article class="ngame">
    <div class="ng-head"><span class="ng-time ${live ? "live" : ""}">${status}</span><span class="muted">${linesTag(g).replace(/^ · /, "")}</span></div>
    ${team(g.away, g.as)}
    <div class="ng-vs"><span>@</span></div>
    ${team(g.home, g.hs)}
    ${linesBlock(g)}
    ${!final ? `<button class="ng-props" data-props="${g.id}">See player props →</button>` : ""}
  </article>`;
}
function linesBlock(g) {
  const L = nhlGameLines(g);
  if (!L) return `<div class="ng-lines empty">Hard Rock moneyline, puck line and total show here after you click Refresh.</div>`;
  const odd = (v) => v == null ? "—" : fmtOdds(v);
  const pt = (v) => v == null ? "" : (v > 0 ? "+" : v < 0 ? "−" : "") + Math.abs(v);
  const row = (t, side) => {
    const ml = L.ml?.[t], pl = L.pl?.[t];
    const tot = L.tot ? `${side === 0 ? "O" : "U"} ${L.tot[0]} <em>${odd(L.tot[side === 0 ? 1 : 2])}</em>` : "—";
    const fav = ml != null && Object.values(L.ml || {}).every((x) => x == null || ml <= x);
    return `<span class="ngl-team">${nLogo(t, "ngl-logo")}${t}</span>
      <span class="ngl-cell ${fav ? "fav" : ""}">${odd(ml)}</span>
      <span class="ngl-cell">${pl ? `${pt(pl[0])} <em>${odd(pl[1])}</em>` : "—"}</span>
      <span class="ngl-cell">${tot}</span>`;
  };
  const when = L.fetched ? new Date(L.fetched).toLocaleString("en-US", { timeZone: ET, month: "short", day: "numeric", hour: "numeric", minute: "2-digit" }) : "";
  return `<div class="ng-lines" role="table" aria-label="Hard Rock game lines">
    <span class="ngl-h">${esc(BOOKS[L.book] || "Hard Rock")}</span><span class="ngl-h">Moneyline</span><span class="ngl-h">Puck line</span><span class="ngl-h">Total</span>
    ${row(g.away, 0)}${row(g.home, 1)}
    ${when ? `<span class="ngl-when">as of ${esc(when)} ET</span>` : ""}</div>`;
}
function renderNHLGames(board) {
  const dayGames = nhlGamesOn(state.date);
  $("slate").textContent = dayGames.length
    ? `${dayGames.length} NHL game${dayGames.length > 1 ? "s" : ""}, ${prettyTime(dayGames.map((g) => g.time).sort()[0])} ET first puck drop` : "No NHL games";
  const TS = ND?.teamStats || {}, early = Object.values(TS).length && Object.values(TS).every((t) => t.gp < 10);
  $("note").textContent = `Offense rank = goals scored per game, defense rank = goals allowed per game (1st is best), across all 32 teams.` +
    (early ? " Early in the season the ranks blend in last season's scoring rate (worth about 10 games) so one or two games don't swing them." : "") +
    ` Starting goalies come from DailyFaceoff: Confirmed means a team or beat reporter said so; Likely and Projected can still change, so check before puck drop. Records from the NHL, built ${ND?.generated || "—"}.`;
  if (!ND || ND.error) {
    board.innerHTML = `<div class="error"><h2>NHL data isn't loaded</h2><p>${ND?.error ? esc(ND.error) : "Put nhl_props.py next to nfl_board.py, then click Refresh."}</p></div>`;
    return;
  }
  if (!dayGames.length) {
    const next = nhlNextDay(state.date);
    board.innerHTML = `<div class="empty"><h2>No NHL games on this date</h2><p>${next ? `Next NHL games: ${prettyDate(next)}.` : "No NHL games loaded for the coming week. Click Refresh."}</p>
      ${next ? `<button class="primary" id="emptyNext">Show ${esc(prettyDate(next))}</button>` : ""}</div>`;
    $("emptyNext")?.addEventListener("click", () => go(next));
    return;
  }
  const hasTS = Object.keys(TS).length, hasG = Object.keys(ND.goalies || {}).length;
  board.innerHTML = `<div class="tdwrap"><div class="tdhead"><h2>Games</h2></div>
    ${!hasTS || !hasG ? `<p class="note">${!hasTS ? (D.shared ? "Team records and ranks load on the next automatic update. " : "Team records and ranks load on the next Refresh through Start NFL Board. ") : ""}${!hasG ? (D.shared ? "Starting goalies load on the next automatic update." : "Starting goalies load on the next Refresh through Start NFL Board.") : ""}</p>` : ""}
    <div class="ngrid">${dayGames.map(nhlGameCard).join("")}</div></div>`;
  board.querySelectorAll("[data-props]").forEach((b) => b.addEventListener("click", () => {
    state.nhlGame = b.dataset.props; state.view = "nhl_pts"; state.lastView.nhl = "nhl_pts"; store.set("board.lastView", state.lastView); render(); window.scrollTo(0, 0); }));
}

function linesTag(g) {
  const L = g.lines ? Object.values(g.lines) : [];
  if (!L.length) return "";
  const firm = L.filter((x) => x.kind === "confirmed" || x.kind === "reported").length;
  return firm === L.length ? " · lines reported" : firm ? " · lines partly reported" : " · lines projected";
}
function probColor(p, a = 1) {
  // red at 0% -> yellow at 50% -> green at 100%
  const v = Math.max(0, Math.min(1, p || 0));
  return `hsla(${Math.round(120 * v)}, 78%, ${Math.round(52 + 6 * Math.sin(Math.PI * v))}%, ${a})`;
}
function ring(p) {
  const R = 30, C = 2 * Math.PI * R, v = Math.max(0, Math.min(1, p));
  return `<div class="ring" role="img" aria-label="${pct(p)} chance"><svg viewBox="0 0 76 76" aria-hidden="true">
    <circle cx="38" cy="38" r="${R}" class="ring-bg"/><circle cx="38" cy="38" r="${R}" class="ring-fg" style="stroke:${probColor(v)};filter:drop-shadow(0 0 5px ${probColor(v, 0.55)})" stroke-dasharray="${(C * v).toFixed(1)} ${C.toFixed(1)}"/></svg>
    <b>${Math.round(v * 100)}<small>%</small></b></div>`;
}
function bigPhoto(r) {
  const ini = esc(r.name.split(" ").map((w) => w[0]).slice(0, 2).join(""));
  const img = r.hs ? `<img src="${esc(r.hs)}" alt="" loading="lazy" data-initials="${ini}" onerror="const s=document.createElement('span');s.className='ini';s.textContent=this.dataset.initials;this.replaceWith(s)">`
    : `<span class="ini">${ini}</span>`;
  return `<div class="pc-photo">${img}</div>`;
}
function nhlFactors(r) {
  // effective multipliers the model applied tonight (see nhl_props.P: LM_B 0.15 points, LM_S 0.20 shots)
  const sog = r.stat === "sog", lm = r.lmf ? Math.pow(r.lmf, sog ? 0.20 : 0.15) : 1;
  return { lm, pp: r.ppf ?? 1, rink: sog ? (r.rink ?? 1) : 1, mkt: sog ? 1 : (r.mkt ?? 1) };
}
function factorPct(x) { const v = Math.round((x - 1) * 100); return v === 0 ? "0%" : `${v > 0 ? "+" : "−"}${Math.abs(v)}%`; }
function nhlCard(r) {
  const posName = r.pos === "D" ? "D" : r.pos === "C" ? "C" : r.pos === "L" ? "LW" : "RW";
  const isFinal = r.res != null, line = r.line;
  if (r.out) return `<article class="pcard outcard" data-row="${esc(r.key)}"><div class="pc-top">${bigPhoto(r)}<div class="pc-who">
      <div class="pc-name">${esc(r.name)}</div><div class="pc-meta">Marked out</div></div>
      <button class="mini" data-nout="${esc(r.key)}">Undo</button></div></article>`;
  const val = !isFinal && r.best.edge != null && r.best.edge >= 0.03;
  const flags = [];
  if (r.lik && !r.lu) flags.push(`<span class="warnpill">Didn't play team's last ${r.dressed[1]}</span>`);
  const F = nhlFactors(r);
  if (Math.abs(F.lm - 1) >= 0.04) flags.push(`<span class="${F.lm > 1 ? "lupill" : "warnpill"}" title="Tonight's DailyFaceoff linemates vs the linemates he usually plays with">${F.lm > 1 ? "Better" : "Weaker"} linemates ${factorPct(F.lm)}</span>`);
  if (!r.career) flags.push(`<span class="warnpill" title="No NHL history: minutes come from his DailyFaceoff line slot and his rate from players in similar roles. Treat edges with extra caution.">Rookie · NHL debut</span>`);
  else if (r.career < 20) flags.push(`<span class="warnpill" title="Little NHL history: the model leans on his line slot and role, so edges are less certain.">Rookie · ${r.career} NHL GP</span>`);
  const S = NHL_STAT[r.stat || "pts"];
  const lineSel = (cur) => `<select class="lsel" data-nml="${esc(r.mk)}" aria-label="Line">${S.lines.map((v) => `<option value="${v}" ${v === cur ? "selected" : ""}>${v}</option>`).join("")}</select>`;
  const price = (side, v) => `<div class="pc-price ${r.best.side === side && r.best.edge > 0 ? "good" : ""}"><small>${side === "Over" ? "Over" : "Under"} ${line}</small><b>${fmtOdds(v) || "—"}</b></div>`;
  const market = r.hasBook
    ? `<div class="pc-market"><div class="pc-line"><small>Hard Rock line</small><b>${line}</b></div>${price("Over", r.over)}${price("Under", r.under)}</div>
       ${r.alts?.length ? `<div class="pc-alts">Also ${r.alts.map((x) => `${x[0]}: ${fmtOdds(x[1]) || "—"} / ${fmtOdds(x[2]) || "—"}`).join(" · ")}</div>` : ""}`
    : isFinal ? ""
    : `<div class="pc-manual"><span>${r.manual ? "Your price" : "No Hard Rock line yet"}</span>
         <div class="manrow">Over ${lineSel(line)}<input class="oin" data-nm="${esc(r.mk)}" placeholder="odds" value="${r.manual ? fmtOdds(r.over).replace("−", "-") : ""}" aria-label="Your Over odds for ${esc(r.name)}"></div></div>`;
  const edge = isFinal
    ? `<div class="pc-edge ${r.hit ? "win" : "loss"}"><span>${r.resv} ${S.unit}</span><b>${r.hit ? `Over ${line} hit` : `Under ${line}`}</b></div>`
    : r.best.edge != null
      ? `<div class="pc-edge ${r.best.edge > 0 ? "pos" : "neg"}"><span>${r.best.side} ${line}</span><b>${r.best.edge >= 0 ? "+" : "−"}${Math.abs(r.best.edge * 100).toFixed(1)}%</b></div>`
      : `<div class="pc-edge none"><span>Edge</span><b>Needs odds</b></div>`;
  const toiTxt = r.toi0 != null && Math.abs(r.toi - r.toi0) >= 0.5 ? ` <i>${r.toi > r.toi0 ? "▲" : "▼"}</i>` : "";
  return `<article class="pcard ${val ? "value" : ""}" data-row="${esc(r.key)}">
    <div class="pc-top">${bigPhoto(r)}
      <div class="pc-who"><div class="pc-name">${esc(r.name)}</div>
        <div class="pc-meta">${nLogo(r.team, "pc-tlogo")}<b>${esc(r.team)}</b>&nbsp;${r.home ? "vs" : "@"} ${esc(r.opp)} · ${prettyTime(r.g.time)}</div>
        <div class="pc-chips"><span class="pospill">${posName}</span>${luChips(r)}${flags.join("")}</div></div>
      ${ring(r.p)}</div>
    ${market}
    ${edge}
    <div class="pc-foot"><span>Fair <b>${fairOdds(r.p)}</b></span><span>Exp <b>${r.lam.toFixed(2)}</b></span>
      <span>TOI <b>${r.toi.toFixed(1)}</b>${toiTxt}</span>${r.stat === "sog"
        ? (r.s10?.length ? `<span>L${r.s10.length} avg <b>${(r.s10.reduce((a, b) => a + b, 0) / r.s10.length).toFixed(1)}</b> SOG</span>` : "")
        : (r.l10[2] ? `<span>L${r.l10[2]} <b>${r.l10[0]}</b> pts</span>` : "")}
      ${!isFinal ? `<button class="mini" data-nout="${esc(r.key)}" title="Hide this player (scratched or injured)">Mark out</button>` : ""}</div>
  </article>`;
}
function nhlRow(r, stat) {
  const line = r.line;
  const unit = NHL_STAT[stat].unit;
  const posName = r.pos === "D" ? "D" : r.pos === "C" ? "C" : r.pos === "L" ? "LW" : "RW";
  const flags = [];
  if (r.lik && !r.lu) flags.push(`<span class="warnpill">Didn't play team's last ${r.dressed[1]}</span>`);
  else if (!r.lu && r.dressed && r.dressed[0] < r.dressed[1]) flags.push(`<span>Played ${r.dressed[0]} of last ${r.dressed[1]}</span>`);
  const F = nhlFactors(r);
  if (Math.abs(F.lm - 1) >= 0.04) flags.push(`<span class="${F.lm > 1 ? "lupill" : "warnpill"}" title="Tonight's DailyFaceoff linemates vs the linemates he usually plays with">${F.lm > 1 ? "Better" : "Weaker"} linemates ${factorPct(F.lm)}</span>`);
  if (!r.career) flags.push(`<span class="warnpill" title="No NHL history: minutes come from his DailyFaceoff line slot and his rate from players in similar roles. Treat edges with extra caution.">Rookie · NHL debut</span>`);
  else if (r.career < 20) flags.push(`<span class="warnpill" title="Little NHL history: the model leans on his line slot and role, so edges are less certain.">Rookie · ${r.career} NHL GP</span>`);
  if (r.out) return `<tr class="outrow" data-row="${esc(r.key)}"><td colspan="4"><div class="pcell">${nPhoto(r)}<div><div class="pname">${esc(r.name)}</div>
      <span class="sub">Marked out.</span><button class="mini" data-nout="${esc(r.key)}">Undo</button></div></div></td></tr>`;
  const isFinal = r.res != null;
  const altTxt = r.alts?.length ? `<span class="sub">Also: ${r.alts.map((x) => `${x[0]} ${fmtOdds(x[1]) || "—"}/${fmtOdds(x[2]) || "—"}`).join(" · ")}</span>` : "";
  const lineSel = (cur) => `<select class="lsel" data-nml="${esc(r.mk)}" aria-label="Line">${NHL_STAT[stat].lines.map((v) => `<option value="${v}" ${v === cur ? "selected" : ""}>${v}</option>`).join("")}</select>`;
  const book = r.hasBook
    ? `<div class="hrline">Hard Rock line <b>${line}</b></div>
       <div class="pricepair"><span><small>Over ${line}</small><b class="${r.best.side === "Over" && r.best.edge > 0 ? "up" : ""}">${fmtOdds(r.over) || "—"}</b></span>
        <span><small>Under ${line}</small><b class="${r.best.side === "Under" && r.best.edge > 0 ? "up" : ""}">${fmtOdds(r.under) || "—"}</b></span></div>
       ${r.noVig != null ? `<span class="sub">No-vig Over ${pct(r.noVig)}</span>` : ""}${altTxt}`
    : isFinal ? `<span class="muted">—</span>`
    : `<div class="manrow">Over ${lineSel(line)}<input class="oin" data-nm="${esc(r.mk)}" placeholder="odds" value="${r.manual ? fmtOdds(r.over).replace("−", "-") : ""}" aria-label="Your Over odds for ${esc(r.name)}"></div>
       <span class="sub">${r.manual ? "Your price (Hard Rock hasn't posted this player)." : "Not posted yet. Click Refresh, or type a price."}</span>`;
  const edge = r.best.edge != null
    ? `<div class="sidepick">${r.best.side}</div><div class="edgeline ${r.best.edge > 0 ? "up" : "down"}">${r.best.edge >= 0 ? "+" : "−"}${Math.abs(r.best.edge * 100).toFixed(1)}%</div>`
    : `<span class="muted">Needs odds</span>`;
  const result = isFinal ? `<span class="nres ${r.hit ? "win" : "loss"}">${r.resv} ${unit} · ${r.hit ? "Over hit" : "Under"}</span>` : "";
  const val = !isFinal && r.best.edge != null && r.best.edge >= 0.03;
  return `<tr class="${val ? "value" : ""}" data-row="${esc(r.key)}">
    <td><div class="pcell">${nPhoto(r)}<div><div class="pname">${esc(r.name)}</div>
      <span class="sub"><span class="pos">${posName}</span>${r.home ? "vs" : "@"} ${esc(r.opp)} · ${prettyTime(r.g.time)}</span>
      <div class="statpills">${luChips(r)}<span>TOI <b>${r.toi.toFixed(1)}</b>${r.toi0 != null && Math.abs(r.toi - r.toi0) >= 0.5 ? ` <small>(${r.toi > r.toi0 ? "up" : "down"} from ${r.toi0.toFixed(1)})</small>` : ""}</span>${stat === "sog" ? (r.s10?.length ? `<span>Last ${r.s10.length}: <b>${r.s10.join(" ")}</b> SOG</span>` : "")
        : (r.l10[2] ? `<span>Last ${r.l10[2]}: <b>${r.l10[0]}</b> pts, <b>${r.l10[1]}</b> ast</span>` : "")}${r.b2b ? `<span class="warnpill">Back-to-back</span>` : ""}${flags.join("")}</div>
      ${result}${!isFinal ? `<button class="mini" data-nout="${esc(r.key)}" title="Hide this player (scratched or injured)">Mark out</button>` : ""}</div></div></td>
    <td><div class="prob"><b>${pct(r.p)}</b><div class="pbar"><i style="width:${Math.min(100, r.p * 100).toFixed(1)}%;background:${probColor(r.p)};box-shadow:0 0 12px ${probColor(r.p, 0.5)}"></i></div></div>
      <span class="sub">Fair ${fairOdds(r.p)} · expects ${r.lam.toFixed(2)} ${unit}</span>
      <span class="sub">${stat === "sog" ? `${(r.s60 ?? 0).toFixed(2)} SOG per 60 · opp/team factor ${(r.senv ?? 1).toFixed(2)}` : `${r.p60.toFixed(2)} per 60 · opp factor ${r.env.toFixed(2)}`}</span>
      ${(() => { const F = nhlFactors(r); return `<span class="sub">Linemates ${factorPct(F.lm)} · PP chances ${factorPct(F.pp)}${stat === "sog" ? ` · rink ${factorPct(F.rink)}` : (r.mkt ? ` · Hard Rock game line ${factorPct(F.mkt)}` : "")}</span>`; })()}</td>
    <td>${book}</td>
    <td class="edgecell">${edge}</td></tr>`;
}

function nhlExport(rows, stat) {
  const out = [["Date", "Time (ET)", "Player", "Pos", "Team", "Opponent", "Home", "Hard Rock line", "Chance over line", "Fair odds", "Expected", "Per 60", "Proj TOI",
    "Over odds", "Under odds", "Pick", "Edge (%)", "EV per $100", "Line", "PP unit", "Status", "Last games", stat === "sog" ? "Last SOG" : "Last pts", stat === "sog" ? "Back-to-back" : "Last ast", "Linemates adj", "PP chances adj", "Rink adj", "Result"]];
  for (const r of [...rows].sort((a, b) => b.p - a.p)) {
    out.push([r.g.day, prettyTime(r.g.time), r.name, r.pos, r.team, r.opp, r.home ? "Yes" : "", r.hasBook || r.manual ? r.line : "", (r.p * 100).toFixed(1) + "%", fairOdds(r.p),
      r.lam.toFixed(3), (stat === "sog" ? r.s60 ?? 0 : r.p60).toFixed(2), r.toi, r.over != null ? fmtOdds(r.over) : "", r.under != null ? fmtOdds(r.under) : "",
      r.best.edge != null ? r.best.side : "", r.best.edge != null ? (r.best.edge * 100).toFixed(1) : "", r.best.ev != null ? r.best.ev.toFixed(0) : "",
      r.lu?.line ?? "", r.lu?.pp || "", r.lu ? (r.lu.status || (r.lu.gtd ? "GTD" : "")) : "", stat === "sog" ? (r.s10 || []).length : r.l10[2], stat === "sog" ? (r.s10 || []).join(" ") : r.l10[0], stat === "sog" ? (r.b2b ? "Yes" : "") : r.l10[1], ...(() => { const F = nhlFactors({ ...r, stat }); return [factorPct(F.lm), factorPct(F.pp), stat === "sog" ? factorPct(F.rink) : ""]; })(), r.resv ?? ""]);
  }
  download(`nhl_${stat === "sog" ? "shots" : "points"}_${state.date}.csv`, out);
}

function setSport(s) {
  state.lastView[state.sport] = state.view;
  state.sport = s; state.view = state.lastView[s] || (s === "nhl" ? "nhl_pts" : "games");
  store.set("board.sport", s); store.set("board.lastView", state.lastView);
  if (s === "nhl" && !nhlGamesOn(state.date).length) { const n = nhlNextDay(shiftDate(state.date, -1)); if (n) state.date = n; }
  render();
}

/* ---------- wire up ---------- */
function go(d) { if (d) { state.date = d; render(); } }
$("prev").addEventListener("click", () => go(shiftDate(state.date, -1)));
$("next").addEventListener("click", () => go(shiftDate(state.date, 1)));
$("today").addEventListener("click", () => go(todayET()));
$("nextGames").addEventListener("click", () => go(state.sport === "nhl" ? nhlNextDay(state.date) : nextGameDay(state.date)));
$("date").addEventListener("change", (e) => go(e.target.value));
$("expand").addEventListener("click", () => { state.openAll = !state.openAll; render(); });
$("export").addEventListener("click", exportGames);
$("exportPlayers").addEventListener("click", exportPlayers);
$("exportTD").addEventListener("click", exportTD);
$("apiKey").value = store.get("nflBoard.oddsApiKey", "");
$("bookSel").value = store.get("nflBoard.book", "hardrockbet_fl");
$("bookSel").addEventListener("change", () => {
  store.set("nflBoard.book", currentBook());
  if (served) fetch("/api/settings", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ book: currentBook() }) });
  render();
});
$("apiKey").addEventListener("change", saveKey);
$("apiKey").addEventListener("keydown", (e) => { if (e.key === "Enter") $("apiKey").blur(); });
$("loadOdds").addEventListener("click", refreshAll);
if (/^#\d{4}-\d{2}-\d{2}$/.test(location.hash)) state.date = location.hash.slice(1);
{ const m = sessionStorage.getItem("nflBoard.lastMsg"); if (m) { oddsMsg = { text: m, err: false }; sessionStorage.removeItem("nflBoard.lastMsg"); } }
if (D.shared && !oddsMsg.text) oddsMsg = { text: `Last updated ${D.generated}. ${D.shared.note}`, err: false };
detectServer().then(render);
document.querySelectorAll(".views button").forEach((b) => b.addEventListener("click", () => {
  state.view = b.dataset.v; state.lastView[state.sport] = state.view; store.set("board.lastView", state.lastView); render(); }));
document.querySelectorAll(".sport button").forEach((b) => b.addEventListener("click", () => setSport(b.dataset.sport)));
document.querySelectorAll(".windows button").forEach((b) => b.addEventListener("click", () => { state.windowKey = b.dataset.w; render(); }));
render();
</script>
</body>
</html>
"""

if __name__ == "__main__":
    main()
