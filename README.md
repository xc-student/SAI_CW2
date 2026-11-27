# Workflow Satisfiability Problem (WSP) Multi-Method Solver

A self-contained Python solver and empirical study for the **Workflow Satisfiability Problem (WSP)**, developed for **COMP3070 Symbolic Artificial Intelligence (2026/2027 Autumn, Group L)**.

The solver supports all five standard WSP constraint types—**Authorisations**, **Binding-of-Duty**, **Separation-of-Duty**, **At-Most-$k$**, and **One-Team**—and classifies every instance as `unsat`, `sat` (unique solution), or `sat` (multiple solutions), with independent witness verification on every returned plan.

## Solving Methods

All three mathematically equivalent formulations are unified in `wsp_solver.py`:

| Method (`--method`) | Formulation | Backend | Key Characteristics |
| :--- | :--- | :--- | :--- |
| `cp-sat` *(default)* | Boolean assignment matrix (B1–B7) | OR-Tools CP-SAT | Strongest scaling reliability on medium-large/unseen instances among the three methods; adaptive search workers (`1` for $n \le 20$, `min(8, cpu_count)` for $n > 20$, overridable via `workers` / `--workers`). |
| `smt` | Finite-domain integer assignment (I1–I7) | Z3 | Compact primary variable encoding ($n$ integer variables) with `ite` cardinality sums and consistent `TimeoutError` handling. |
| `pattern` | Canonical step partitions + bipartite matching (P1–P7) | Pure Python (stdlib) | Adapts Karapetyan et al. (2019) to support user-dependent `one-team` constraints via single-pass domain tightening, mid-search pigeonhole pruning, incremental team backtracking, and edge-forbidding rematching. |

## Verification & Benchmark Highlights

- **Correctness**: 100% pass rate across **334** targeted checks (official Examples 1–8, 100 seeded random workflows verified against brute-force enumeration, parser/timeout edge cases, `helper.py` integration, and worker policy checks) and **100% cross-method / ground-truth agreement** across all completed runs in the **537-run** single-core benchmark (179 unique instances) plus a **150-run** multi-worker CP-SAT ablation.
- **Small & Multi-Constraint Workflows ($n \le 10$)**: `pattern` achieves sub-millisecond runtimes—averaging **0.22 ms** on `5-constraint` ($n=10, m=50$), ~**318×** faster than `cp-sat` (71.29 ms) and ~**563×** faster than `smt` (126.10 ms).
- **Larger Workflows ($n = 20\text{–}60$)**: `cp-sat` overtakes `pattern` on `example11`/`example12` ($n=20, m=100$) and solves `example17` (SAT) and `example18` (UNSAT) under extended 300 s budgets.

## Repository Structure

```text
.
├── wsp_solver.py                                  # Unified single-file WSP solver (CP-SAT, SMT, Pattern)
├── COMP3070_Coursework_2_Final_Report_Group_L.pdf # Full mathematical formulations & empirical report
├── requirements.txt                               # Python dependencies
└── README.md
```
