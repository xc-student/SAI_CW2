"""COMP3070 Coursework 2: Workflow Satisfiability Problem (WSP) Solver.

Group: Group L

Attribution and Original Work:
- The public Solver(filename, **kwargs) return schema (sat, sol, mul_sol,
  exe_time) follows the supplied coursework template (template.py / helper.py).
- The pattern-based partition solver adapts the canonical partition framework of
  Karapetyan et al. (2019, JAIR, https://arxiv.org/abs/1604.05636) to handle
  the coursework's one-team constraints and global uniqueness verification.
- All input parsing, Z3 (SMT) integer encoding, OR-Tools (CP-SAT) Boolean
  matrix encoding, one-team domain pre-tightening and pigeonhole pruning,
  augmenting-path bipartite matching, and independent witness validation are
  our group's own implementation.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
from time import perf_counter
from typing import Iterator, Optional


@dataclass
class Workflow:
    """Parsed WSP instance using zero-based internal step and user indices."""

    steps: int
    users: int
    domains: list[set[int]]
    pairs: list[tuple[int, int, bool]] = field(default_factory=list)
    limits: list[tuple[tuple[int, ...], int]] = field(default_factory=list)
    teams: list[tuple[tuple[int, ...], list[set[int]]]] = field(default_factory=list)


def read_workflow(filename: str | Path) -> Workflow:
    """Parse a WSP text instance into a Workflow dataclass.

    Handles UTF-8 BOM, case-insensitive constraint names, extra whitespace,
    implicit full authorisation for unlisted users, and empty authorisation
    lists (e.g., ``Authorisations u1``).
    """
    lines = [
        line.strip().lower()
        for line in Path(filename).read_text(encoding="utf-8-sig").splitlines()
        if line.strip()
    ]
    n, m, count = (int(line.split(":")[1]) for line in lines[:3])
    if len(lines) != 3 + count:
        raise ValueError("Constraint count mismatch")

    # Start with every user authorised for every step; narrow per record.
    w = Workflow(n, m, [set(range(m)) for _ in range(n)])
    for line in lines[3:]:
        tokens = line.split()
        name = tokens[0]
        steps = tuple(int(v) - 1 for v in re.findall(r"s(\d+)", line))
        if name == "authorisations":
            user = int(re.search(r"u(\d+)", line)[1]) - 1
            for s in set(range(n)).difference(steps):
                w.domains[s].discard(user)
        elif name in {"binding-of-duty", "separation-of-duty"}:
            w.pairs.append((*steps, name == "binding-of-duty"))
        elif name == "at-most-k":
            w.limits.append((steps, int(tokens[1])))
        elif name == "one-team":
            groups = [
                set(int(v) - 1 for v in re.findall(r"u(\d+)", grp))
                for grp in re.findall(r"\(([^)]*)\)", line)
            ]
            w.teams.append((steps, groups))
        else:
            raise ValueError(f"Unknown constraint record: {line}")
    return w


def valid(w: Workflow, plan: tuple[int, ...]) -> bool:
    """Independently verify that a decoded step-to-user plan satisfies all rules."""
    return (
        len(plan) == w.steps
        and all(u in w.domains[s] for s, u in enumerate(plan))
        and all((plan[a] == plan[b]) == equal for a, b, equal in w.pairs)
        and all(len({plan[s] for s in steps}) <= k for steps, k in w.limits)
        and all(
            any(all(plan[s] in team for s in steps) for team in teams)
            for steps, teams in w.teams
        )
    )


def smt(w: Workflow, timeout: Optional[float] = None) -> Iterator[tuple[int, ...]]:
    """Solve WSP via Z3 integer encoding (Formulas I1-I7) and yield distinct plans."""
    import z3

    if any(not d for d in w.domains):
        return
    if w.steps == 0:
        if all(bool(teams) for _, teams in w.teams):
            yield ()
        return

    deadline = None if timeout is None else perf_counter() + timeout
    solver = z3.Solver()

    # I1 & I2: One integer variable per step restricted to authorised domain D_s.
    x = [z3.Int(f"user_{s}") for s in range(w.steps)]
    for var, domain in zip(x, w.domains):
        solver.add(z3.Or([var == u for u in sorted(domain)]))

    # I3 & I4: Binding-of-duty (equality) and separation-of-duty (disequality).
    for a, b, equal in w.pairs:
        solver.add((x[a] == x[b]) if equal else (x[a] != x[b]))

    # I5: At-most-k distinct users via indicator sum over authorised scope users.
    for steps, k in w.limits:
        active_users = (
            sorted(set().union(*(w.domains[s] for s in steps))) if steps else []
        )
        if len(active_users) <= k:
            continue
        used = [
            z3.Or([x[s] == u for s in steps if u in w.domains[s]])
            for u in active_users
        ]
        solver.add(z3.Sum([z3.If(hit, 1, 0) for hit in used]) <= k)

    # I6: One-team constraint with dead-team pre-filtering against step domains.
    for steps, teams in w.teams:
        team_clauses = []
        for team in teams:
            if all(team & w.domains[s] for s in steps):
                step_exprs = [
                    z3.Or([x[s] == u for u in sorted(team & w.domains[s])])
                    for s in steps
                ]
                team_clauses.append(z3.And(step_exprs))
        if not team_clauses:
            return
        solver.add(z3.Or(team_clauses))

    while True:
        if deadline is not None:
            remaining = deadline - perf_counter()
            if remaining <= 0:
                raise TimeoutError("SMT solver timed out")
            solver.set("timeout", max(1, int(remaining * 1000)))

        state = solver.check()
        if state == z3.unsat:
            return
        if state != z3.sat:
            reason = solver.reason_unknown()
            if deadline is not None and (
                "timeout" in reason.lower() or "canceled" in reason.lower()
            ):
                raise TimeoutError("SMT solver timed out")
            raise RuntimeError(reason)

        model = solver.model()
        plan = tuple(model.evaluate(v, model_completion=True).as_long() for v in x)
        yield plan

        # I7: Blocking disjunction excluding the current assignment.
        solver.add(z3.Or([v != u for v, u in zip(x, plan)]))


def default_cp_sat_workers(steps: int) -> int:
    """Use 1 worker for small/medium workflows and up to 8 workers for n > 20."""
    return 1 if steps <= 20 else min(8, os.cpu_count() or 1)


def cp_sat(
    w: Workflow,
    workers: Optional[int] = None,
    timeout: Optional[float] = None,
) -> Iterator[tuple[int, ...]]:
    """Solve WSP via OR-Tools CP-SAT Boolean matrix (Formulas B1-B7)."""
    from ortools.sat.python import cp_model

    if any(not d for d in w.domains):
        return
    if w.steps == 0:
        if all(bool(teams) for _, teams in w.teams):
            yield ()
        return

    deadline = None if timeout is None else perf_counter() + timeout
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    # Support both newer snake_case (OR-Tools >= 9.10) and legacy CamelCase APIs.
    new_bool = getattr(model, "new_bool_var", None) or model.NewBoolVar
    add_exact_one = getattr(model, "add_exactly_one", None) or model.AddExactlyOne
    add_cons = getattr(model, "add", None) or model.Add
    solve_fn = getattr(solver, "solve", None) or solver.Solve
    get_val = getattr(solver, "value", None) or solver.Value
    status_name = getattr(solver, "status_name", None) or solver.StatusName

    # B1 & B2: Boolean step-user matrix, one user per row, unauthorised bits = 0.
    rows = [
        [new_bool(f"b_{s}_{u}") for u in range(w.users)]
        for s in range(w.steps)
    ]
    for s, row in enumerate(rows):
        add_exact_one(row)
        for u in set(range(w.users)) - w.domains[s]:
            add_cons(row[u] == 0)

    # B3 & B4: Binding (row equality) and separation (row sum <= 1).
    for a, b, equal in w.pairs:
        for left, right in zip(rows[a], rows[b]):
            add_cons(left == right if equal else left + right <= 1)

    # B5: At-most-k distinct users via two-sided occurrence indicators.
    for idx, (steps, k) in enumerate(w.limits):
        active_users = (
            sorted(set().union(*(w.domains[s] for s in steps))) if steps else []
        )
        if len(active_users) <= k:
            continue
        used = []
        for u in active_users:
            flag = new_bool(f"used_{idx}_{u}")
            hits = [rows[s][u] for s in steps if u in w.domains[s]]
            for hit in hits:
                add_cons(flag >= hit)
            add_cons(flag <= sum(hits))
            used.append(flag)
        add_cons(sum(used) <= k)

    # B6: One-team constraint with dead-team pre-filtering.
    for idx, (steps, teams) in enumerate(w.teams):
        valid_teams = [t for t in teams if all(t & w.domains[s] for s in steps)]
        if not valid_teams:
            return
        selected = [new_bool(f"team_{idx}_{h}") for h in range(len(valid_teams))]
        add_exact_one(selected)
        for team, flag in zip(valid_teams, selected):
            for s in steps:
                add_cons(sum(rows[s][u] for u in sorted(team & w.domains[s])) >= flag)

    num_workers = default_cp_sat_workers(w.steps) if workers is None else workers
    if num_workers < 1:
        raise ValueError("workers must be >= 1")
    solver.parameters.num_search_workers = num_workers

    while True:
        if deadline is not None:
            remaining = deadline - perf_counter()
            if remaining <= 0:
                raise TimeoutError("CP-SAT solver timed out")
            solver.parameters.max_time_in_seconds = remaining

        status = solve_fn(model)
        if status == cp_model.INFEASIBLE:
            return
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            if status == cp_model.UNKNOWN and deadline is not None:
                raise TimeoutError("CP-SAT solver timed out")
            raise RuntimeError(status_name(status))

        plan = tuple(
            next(u for u, bit in enumerate(row) if get_val(bit))
            for row in rows
        )
        yield plan

        # B7: Linear no-good cut excluding the decoded step assignment.
        add_cons(sum(rows[s][u] for s, u in enumerate(plan)) < w.steps)


def matching(
    domains: list[set[int]],
    banned: Optional[tuple[int, int]] = None,
) -> Optional[list[int]]:
    """Find a covering bipartite matching from blocks to distinct users.

    Uses MRV ordering on block domains and DFS augmenting paths, optionally
    forbidding one edge ``(block, user)`` to probe for an alternative matching.
    """
    owner: dict[int, int] = {}

    def augment(block: int, seen: set[int]) -> bool:
        for user in sorted(domains[block]):
            if user in seen or (block, user) == banned:
                continue
            seen.add(user)
            if user not in owner or augment(owner[user], seen):
                owner[user] = block
                return True
        return False

    for block in sorted(range(len(domains)), key=lambda b: len(domains[b])):
        if not augment(block, set()):
            return None

    answer: list[Optional[int]] = [None] * len(domains)
    for user, block in owner.items():
        answer[block] = user
    return answer  # type: ignore[return-value]


def patterns(
    w: Workflow,
    timeout: Optional[float] = None,
) -> Iterator[tuple[int, ...]]:
    """Solve WSP via canonical step partitions and bipartite matching (P1-P7).

    Adapts the pattern-based approach of Karapetyan et al. (2019, JAIR) with:
    1) Local domain pre-tightening from feasible one-team unions;
    2) Step-indexed duty/count checks and mid-search one-team pigeonhole pruning;
    3) Incremental team-choice backtracking instead of full Cartesian products;
    4) Edge-forbidding rematching and global plan deduplication for uniqueness.
    """
    if w.steps == 0:
        if all(bool(teams) for _, teams in w.teams):
            yield ()
        return

    deadline = None if timeout is None else perf_counter() + timeout

    # Local copy of domains so caller-owned Workflow objects are never mutated.
    eff_domains = [d.copy() for d in w.domains]
    if any(not d for d in eff_domains):
        return

    # Pre-filter infeasible candidate teams and tighten step domains by team union.
    active_teams: list[tuple[tuple[int, ...], list[set[int]]]] = []
    for scope, teams in w.teams:
        valid_t = [t for t in teams if all(t & eff_domains[s] for s in scope)]
        if not valid_t:
            return
        allowed = set().union(*valid_t)
        for s in scope:
            eff_domains[s] &= allowed
            if not eff_domains[s]:
                return
        # Constraints with a single surviving team are already enforced by eff_domains.
        if len(valid_t) > 1:
            active_teams.append((scope, valid_t))
    active_teams.sort(key=lambda item: len(item[1]))

    # Index binary and count constraints by step to avoid full-list scans per node.
    pairs_at: list[list[tuple[int, int, bool]]] = [[] for _ in range(w.steps)]
    for a, b, equal in w.pairs:
        pairs_at[max(a, b)].append((a, b, equal))

    limits_at: list[list[tuple[tuple[int, ...], int]]] = [[] for _ in range(w.steps)]
    for scope, k in w.limits:
        for s in scope:
            limits_at[s].append((scope, k))

    labels: list[int] = []
    domains: list[set[int]] = []
    found: set[tuple[int, ...]] = set()

    def choose_team(idx: int, cand_domains: list[set[int]]) -> Iterator[tuple[int, ...]]:
        """Incrementally select one team per active one-team record (P6-P7)."""
        if deadline is not None and perf_counter() > deadline:
            raise TimeoutError("Pattern solver timed out")

        if idx == len(active_teams):
            first = matching(cand_domains)
            if first is None:
                return
            # Every alternative matching of the same graph omits at least one edge of first.
            for banned in [None, *enumerate(first)]:
                match = first if banned is None else matching(cand_domains, banned)
                if match is not None:
                    plan = tuple(match[b] for b in labels)
                    if plan not in found:
                        found.add(plan)
                        yield plan
                    if len(found) == 2:
                        return
            return

        scope, teams = active_teams[idx]
        touched = {labels[i] for i in scope}
        for team in teams:
            if len(team) < len(touched):
                continue
            next_domains = list(cand_domains)
            ok = True
            union_users: set[int] = set()
            for blk in touched:
                inter = cand_domains[blk] & team
                if not inter:
                    ok = False
                    break
                next_domains[blk] = inter
                union_users |= inter
            # Pigeonhole bound: distinct blocks require at least |touched| distinct users.
            if ok and len(union_users) >= len(touched):
                yield from choose_team(idx + 1, next_domains)
                if len(found) == 2:
                    return

    def visit() -> Iterator[tuple[int, ...]]:
        """Enumerate canonical partitions in first-occurrence order (P1-P5)."""
        if deadline is not None and perf_counter() > deadline:
            raise TimeoutError("Pattern solver timed out")

        s = len(labels)
        if s == w.steps:
            yield from choose_team(0, domains)
            return

        for b in range(min(len(domains) + 1, w.users)):
            new = b == len(domains)
            old = None if new else domains[b]
            eligible = eff_domains[s] if new else old & eff_domains[s]
            if not eligible:
                continue

            labels.append(b)
            if new:
                domains.append(eligible)
            else:
                domains[b] = eligible

            ok = (
                all((labels[i] == labels[j]) == equal for i, j, equal in pairs_at[s])
                and all(
                    len({labels[i] for i in scope if i <= s}) <= k
                    for scope, k in limits_at[s]
                )
            )
            # Mid-search one-team pruning for every constraint touching modified block b.
            if ok and active_teams:
                for scope, teams in active_teams:
                    touched = {labels[i] for i in scope if i <= s}
                    if b not in touched:
                        continue
                    if not any(
                        len(t) >= len(touched)
                        and all(domains[blk] & t for blk in touched)
                        and len(set().union(*(domains[blk] & t for blk in touched)))
                        >= len(touched)
                        for t in teams
                    ):
                        ok = False
                        break

            if ok:
                yield from visit()

            labels.pop()
            if new:
                domains.pop()
            else:
                domains[b] = old
            if len(found) == 2:
                return

    yield from visit()


METHODS = {"smt": smt, "cp-sat": cp_sat, "pattern": patterns}


def Solver(filename: str | Path, **kwargs) -> dict[str, object]:
    """Solve a WSP instance file and return the coursework template dictionary.

    Defaults to ``method="cp-sat"`` with adaptive search workers (``1`` when
    ``n <= 20`` to avoid thread-pool overhead, scaling up to
    ``min(8, os.cpu_count() or 1)`` when ``n > 20``). Optional keyword arguments:
    ``method``, ``timeout`` (seconds), and ``workers`` (int override for ``cp-sat``).
    """
    start = perf_counter()
    w = read_workflow(filename)
    method = kwargs.get("method", "cp-sat")
    timeout = kwargs.get("timeout")

    if method == "cp-sat":
        plans = cp_sat(w, workers=kwargs.get("workers"), timeout=timeout)
    elif method in METHODS:
        plans = METHODS[method](w, timeout=timeout)
    else:
        raise ValueError(f"Unknown solver method: {method}")

    first = next(plans, None)
    if first is not None and not valid(w, first):
        raise ValueError("Solver produced an invalid assignment")

    second: Optional[tuple[int, ...]] = None
    second_timed_out = False
    if first is not None:
        try:
            second = next(plans, None)
        except TimeoutError:
            second_timed_out = True

    if second is not None:
        if not valid(w, second):
            raise ValueError("Solver produced an invalid assignment")
        if first == second:
            raise ValueError("Duplicate assignment")

    return dict(
        sat="unsat" if first is None else "sat",
        sol="" if first is None else [f"s{i + 1}: u{u + 1}" for i, u in enumerate(first)],
        mul_sol=(
            ""
            if first is None
            else (
                "unknown (timeout)"
                if second_timed_out
                else (
                    "this is the only solution"
                    if second is None
                    else "other solutions exist"
                )
            )
        ),
        exe_time=f"{1000 * (perf_counter() - start):.3f}ms",
    )


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description="COMP3070 Workflow Satisfiability Solver")
    cli.add_argument("filename", help="Path to a WSP instance file")
    cli.add_argument(
        "--method",
        choices=METHODS,
        default="cp-sat",
        help="Solving backend (default: cp-sat)",
    )
    cli.add_argument(
        "--timeout",
        type=float,
        default=None,
        help="Optional per-instance timeout in seconds",
    )
    cli.add_argument(
        "--workers",
        type=int,
        default=None,
        help="Search workers for cp-sat (default: adaptive, 1 if n <= 20 else min(8, cpu_count))",
    )
    args = cli.parse_args()
    print(
        json.dumps(
            Solver(
                args.filename,
                method=args.method,
                timeout=args.timeout,
                workers=args.workers,
            ),
            indent=2,
        )
    )