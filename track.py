"""Results tracker for the GameDay Edge board (NHL points and shots props vs Hard Rock prices).

Kept separate from the web page: reads the freshly built board (site/index.html), and maintains
  tracking/nhl_props_log.csv   one row per player, game and market that Hard Rock priced
  tracking/summary.md          record, profit and calibration so far
Rules:
  - Before a game starts, its rows are refreshed on every build (latest price and latest model number),
    and the model number at the first price we saw is kept too.
  - Once a game has started, prices and model numbers are frozen; when it is final the result is filled in.
Usage: python track.py site/index.html tracking
"""
import csv
import json
import math
import re
import sys
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

ET = ZoneInfo("America/New_York")
MODEL_VERSION = "2026-10-01"   # bump when the model changes, so results can be split by version
FIELDS = ["date", "game_id", "matchup", "player_id", "player", "team", "opp", "pos", "market", "line", "over", "under",
          "no_vig_over", "model_exp", "model_p_over", "pick", "pick_price", "pick_edge", "pick_ev_per_100",
          "model_p_over_first", "pick_first", "line_slot", "pp_unit", "lineup_status", "odds_fetched",
          "first_logged", "last_updated", "model_version", "result", "outcome", "profit_per_100"]
MARKETS = {"pts": "points", "sog": "shots"}


def pois_over(lam, line):
    k, cdf, term = int(math.floor(line)), 0.0, math.exp(-lam)
    for i in range(k + 1):
        if i:
            term *= lam / i
        cdf += term
    return max(0.0, min(1.0, 1 - cdf))


def implied(price):
    return 100 / (price + 100) if price > 0 else -price / (-price + 100)


def profit(price):
    return price if price > 0 else 10000 / -price


def main_line(lines):
    """Hard Rock's main line: the one priced closest to even money (both sides posted preferred) - same rule as the board."""
    lines = [x for x in lines if x[1] is not None or x[2] is not None]
    if not lines:
        return None
    both = [x for x in lines if x[1] is not None and x[2] is not None]
    pool = both or lines
    dist = lambda x: abs((implied(x[1]) if x[1] is not None else 1 - implied(x[2])) - 0.5)
    return min(pool, key=dist)


def load_board(path):
    html = Path(path).read_text(encoding="utf-8")
    m = re.search(r'<script type="application/json" id="nfl-data">(.*?)</script>', html, re.S)
    return json.loads(m.group(1).replace("<\\/", "</"))


def rows_from_board(data, now):
    n = data.get("nhl") or {}
    games = {str(g["id"]): g for g in n.get("games", [])}
    odds, times = n.get("odds", {}), n.get("oddsTimes", {})
    out = {}
    for gid, players in odds.items():
        g = games.get(str(gid))
        if not g:
            continue
        by_pid = {str(r["pid"]): r for r in (n.get("proj", {}).get(str(gid)) or n.get("proj", {}).get(gid) or [])}
        for pid, markets in players.items():
            r = by_pid.get(str(pid))
            if not r:
                continue
            for stat, lines in markets.items():
                if stat not in MARKETS:
                    continue
                if lines and isinstance(lines[0], (int, float)):
                    lines = [lines]
                ml = main_line(lines)
                if not ml:
                    continue
                line, over, under = ml
                lam = r.get(stat)
                if lam is None:
                    continue
                p = pois_over(lam, line)
                cands = []
                if over is not None:
                    cands.append(("Over", over, p - implied(over), p * profit(over) - (1 - p) * 100))
                if under is not None:
                    cands.append(("Under", under, (1 - p) - implied(under), (1 - p) * profit(under) - p * 100))
                side, price, edge, ev = max(cands, key=lambda c: c[3])
                nv = implied(over) / (implied(over) + implied(under)) if over is not None and under is not None else None
                res = r.get("res")
                lu = r.get("lu") or {}
                key = (str(gid), str(pid), MARKETS[stat])
                out[key] = {
                    "date": g["day"], "game_id": gid, "matchup": f'{g["away"]} @ {g["home"]}', "player_id": pid,
                    "player": r["name"], "team": r["team"], "opp": r["opp"], "pos": r["pos"], "market": MARKETS[stat],
                    "line": line, "over": over, "under": under, "no_vig_over": round(nv, 4) if nv is not None else "",
                    "model_exp": round(lam, 3), "model_p_over": round(p, 4), "pick": side, "pick_price": price,
                    "pick_edge": round(edge, 4), "pick_ev_per_100": round(ev, 1),
                    "line_slot": lu.get("line") or "", "pp_unit": lu.get("pp") or "", "lineup_status": lu.get("status") or "",
                    "odds_fetched": times.get(str(gid), times.get(gid, "")), "last_updated": now, "model_version": MODEL_VERSION,
                    "_started": g.get("state") not in ("FUT", "PRE"),
                    "_result": None if res is None else res.get(stat),
                }
    return out


def settle(row):
    if row.get("result") in ("", None):
        return
    res, line = float(row["result"]), float(row["line"])
    if res == line:
        row["outcome"], row["profit_per_100"] = "push", 0
        return
    won = (res > line) == (row["pick"] == "Over")
    row["outcome"] = "win" if won else "loss"
    row["profit_per_100"] = round(profit(float(row["pick_price"])), 1) if won else -100


def summarize(rows):
    done = [r for r in rows if r.get("outcome") in ("win", "loss", "push")]
    lines = ["# NHL props vs Hard Rock: results so far", "",
             f"Updated {datetime.now(ET).strftime('%b %d, %Y %I:%M %p ET')}. Every player Hard Rock priced is logged; "
             "the pick is the side (Over or Under) the model rated better at Hard Rock's price. Profit assumes $100 on every pick.", ""]
    if not done:
        lines.append(f"No settled games yet ({len(rows)} props logged and waiting for results).")
        return "\n".join(lines) + "\n"

    def block(title, rs):
        w = sum(r["outcome"] == "win" for r in rs); l = sum(r["outcome"] == "loss" for r in rs)
        pr = sum(float(r["profit_per_100"]) for r in rs)
        roi = pr / (100 * len(rs)) if rs else 0
        return f"| {title} | {len(rs)} | {w}-{l} | {w / (w + l):.1%} | {pr:+,.0f} | {roi:+.1%} |" if w + l else f"| {title} | {len(rs)} | - | - | - | - |"

    hdr = ["| Group | Picks | W-L | Win % | Profit ($100 each) | ROI |", "|---|---|---|---|---|---|"]
    lines += ["## Record", ""] + hdr + [block("All", done)]
    for m in ("points", "shots"):
        lines.append(block(m.title(), [r for r in done if r["market"] == m]))
    for side in ("Over", "Under"):
        lines.append(block(f"{side} picks", [r for r in done if r["pick"] == side]))
    lines += ["", "## By model edge", ""] + hdr
    for lo, hi, lab in ((-1, 0, "Negative edge"), (0, 0.03, "0-3%"), (0.03, 0.06, "3-6% (value plays)"), (0.06, 0.10, "6-10%"), (0.10, 9, "10%+")):
        lines.append(block(lab, [r for r in done if lo <= float(r["pick_edge"]) < hi]))
    lines += ["", "## Calibration (does 'X% chance' happen X% of the time?)", "",
              "| Market | Model chance of Over | Props | Actual Over rate | Hard Rock no-vig |", "|---|---|---|---|---|"]
    for m in ("points", "shots"):
        rs = [r for r in done if r["market"] == m]
        for lo in (0, 0.2, 0.4, 0.6, 0.8):
            b = [r for r in rs if lo <= float(r["model_p_over"]) < lo + 0.2]
            if not b:
                continue
            act = sum(float(r["result"]) > float(r["line"]) for r in b) / len(b)
            nv = [float(r["no_vig_over"]) for r in b if r["no_vig_over"] not in ("", None)]
            lines.append(f"| {m} | {lo:.0%}-{lo + 0.2:.0%} | {len(b)} | {act:.1%} | {sum(nv) / len(nv):.1%} |" if nv else
                         f"| {m} | {lo:.0%}-{lo + 0.2:.0%} | {len(b)} | {act:.1%} | - |")
    lines += ["", f"Settled props: {len(done)}. Waiting for results: {len(rows) - len(done)}. "
              "Small samples swing a lot; judge after a few hundred settled picks."]
    return "\n".join(lines) + "\n"


def main(board_path, folder):
    folder = Path(folder); folder.mkdir(parents=True, exist_ok=True)
    log = folder / "nhl_props_log.csv"
    now = datetime.now(ET).strftime("%Y-%m-%d %H:%M")
    existing = {}
    if log.exists():
        with log.open(newline="", encoding="utf-8") as f:
            for r in csv.DictReader(f):
                existing[(r["game_id"], r["player_id"], r["market"])] = r
    fresh = rows_from_board(load_board(board_path), now)
    for key, new in fresh.items():
        old = existing.get(key)
        started, result = new.pop("_started"), new.pop("_result")
        if old is None:
            if started and result is None:
                continue          # first seen mid-game: no pre-game snapshot, skip
            new["first_logged"] = now
            new["model_p_over_first"], new["pick_first"] = new["model_p_over"], new["pick"]
            new["result"] = "" if result is None else result
            existing[key] = new
        elif not started:
            new["first_logged"] = old.get("first_logged") or now
            new["model_p_over_first"] = old.get("model_p_over_first") or new["model_p_over"]
            new["pick_first"] = old.get("pick_first") or new["pick"]
            new["result"] = ""
            existing[key] = new
        elif result is not None and old.get("result") in ("", None):
            old["result"] = result
    for r in existing.values():
        settle(r)
    rows = sorted(existing.values(), key=lambda r: (r["date"], r["game_id"], r["market"], r["player"]))
    with log.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)
    (folder / "summary.md").write_text(summarize(rows), encoding="utf-8")
    print(f"Tracking: {len(rows)} props logged, {sum(r.get('outcome') in ('win', 'loss', 'push') for r in rows)} settled.")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "site/index.html", sys.argv[2] if len(sys.argv) > 2 else "tracking")
