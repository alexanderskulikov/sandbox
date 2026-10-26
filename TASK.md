# Task: a CDCL SAT solver from scratch

Write a SAT solver for CNF formulas in pure Python, from scratch, and give a sceptical reader good reasons to trust its answers.

## Interface

```
python3 solver.py FORMULA.cnf [--proof PROOF.drat]
```

- Input: a formula in DIMACS CNF format.
- Output, in the format of the SAT Competition:
  - `s SATISFIABLE`, followed by `v` lines that give a value to every variable and end with `0`;
  - or `s UNSATISFIABLE`.
- Exit code: 10 if satisfiable, 20 if unsatisfiable.
- With `--proof`, for an unsatisfiable formula, write a DRAT proof to `PROOF.drat`: the learned clauses in the order they were learned, optionally `d` lines for deleted clauses, and the empty clause `0` at the end.

## Algorithm

Conflict-driven clause learning (CDCL):
- two watched literals;
- first-UIP clause learning with non-chronological backjumping;
- a decision heuristic such as VSIDS;
- restarts;
- phase saving.

Deleting learned clauses and preprocessing are optional.

## Rules

1. Python standard library only; no external packages.
2. `solver.py` must not call or contain any existing SAT, SMT or constraint solver, and must not start other processes.
3. The answer must not depend on the name or path of the formula's file, or on `bench/answers.csv`. The answers file is only for your tests.
4. Do not modify anything in `bench/`.
5. Do not weaken a test to make it pass. If something does not work, say so in the report.

Your solver will also be checked independently, on formulas you have not seen.

## Checking

Checking the answers is the main part of the task.

- Write `check.py`, which checks a satisfying assignment against the formula independently of the solver's code.
- Compare your answers with `bench/answers.csv`.
- Generate many small random formulas (up to about 12 variables) and compare the solver with a brute-force search.
- Check the DRAT proofs of unsatisfiable formulas with a checker you write; checking that every lemma is RUP is enough for a CDCL solver.
- Put the tests in `tests/`, runnable with one command.

## Performance

Each formula in `bench/` should take at most 60 seconds on a laptop. Report the times for each size.

## Report

Write `REPORT.md`:
- what is implemented;
- how the answers were checked, and what the checks do and do not cover;
- a table of results on `bench/`: for each size, the number of formulas, how many were solved, and the mean and maximum time;
- what does not work, was not checked, or you are unsure about;
- decisions you made without asking.

## Process

Work on your own; do not ask questions. Make reasonable decisions and record them in `REPORT.md`. Commit after each milestone with a clear message, and push the branch.
