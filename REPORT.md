# CDCL SAT solver in pure Python: report

## Summary

* `solver.py` is a CDCL solver that uses only the Python standard library.
  It solves all 80 formulas in `bench/` correctly. The slowest takes 0.90 s,
  against the 60 s limit.
* Every answer it gives can be checked independently:
  * `check.py` checks satisfying assignments.
  * `drat_check.py` checks DRAT proofs of unsatisfiability: every lemma must
    be RUP.
  * Neither checker shares code with the solver.
* Every bench answer was checked. That means 43 models and 37 DRAT proofs.
* `python3 tests/run_tests.py` runs the whole test suite. It takes about 40 s
  and passes on Python 3.11, 3.12 and 3.13.
* Not every check covers everything. The section
  "What the checks cover and what they do not" says where the trust comes
  from and where its limits are.

## Files

| file | purpose |
|---|---|
| `solver.py` | the solver: `python3 solver.py FORMULA.cnf [--proof PROOF.drat] [-v]` |
| `check.py` | checks the solver's output: `python3 check.py FORMULA.cnf OUTPUT [--proof PROOF.drat]`. Exit 0 = verified, 1 = rejected, 2 = an UNSAT claim with no proof |
| `drat_check.py` | forward RUP checker for DRAT proofs: `python3 drat_check.py FORMULA.cnf PROOF.drat` |
| `tests/run_tests.py` | runs every test (`python3 -m unittest discover -s tests` also works) |
| `tests/test_random.py` | random formulas compared with brute force, with every certificate checked |
| `tests/test_structured.py` | families with known answers, plus edge cases of the input and output format through the command line |
| `tests/test_checkers.py` | tests of the checkers themselves |
| `tests/test_bench.py` | `bench/` compared with `bench/answers.csv`, every certificate checked, 60 s limit |
| `tests/common.py` | generators and independent "ground truth" deciders used by the tests |
| `tests/mutation_check.py` | plants 17 bugs in a copy of the solver and checks that the tests catch each one. Slow, so it is not part of `run_tests.py` |
| `tests/bench_report.py` | produces the bench timing table below |
| `tests/scaling_report.py` | times random 3-SAT instances larger than those in `bench/` |

## What is implemented

**Input.** `solver.py` reads DIMACS CNF leniently:
* comment lines anywhere;
* clauses spread over several lines, or several clauses on one line;
* an optional SATLIB-style `%` end marker;
* variables beyond the header count (the larger number is used);
* a missing final `0`.

Then it cleans the clauses:
* duplicate literals are removed;
* tautologies are dropped;
* an empty clause means UNSAT at once;
* unit clauses are assigned at level 0.

There is no other preprocessing.

**Search.** Conflict-driven clause learning:
* **Two watched literals.** The watched literals of a clause are always
  `c[0]` and `c[1]`. A clause sits exactly in the watch lists of those two
  literals. When a clause becomes unit, the literal it implies is moved to
  `c[0]`. Binary and ternary clauses are not treated specially.
* **First-UIP learning.** The learned clause is then minimised recursively, in
  the MiniSat style. A literal is dropped if the other literals imply it
  through reason clauses.
* **Non-chronological backjumping.** The solver jumps back to the
  second-highest decision level in the learned clause. The learned clause is
  then unit, and its literal is asserted at that level.
* **VSIDS.** Every variable seen during conflict analysis gets an activity
  bump. Decay is 0.95, done by growing the increment, and activities are
  rescaled at 1e100. The next decision comes from a binary heap (`heapq`)
  with lazy deletion. A `fresh` flag per variable avoids pushing entries that
  are already up to date.
* **Restarts** follow the Luby sequence with a unit of 100 conflicts.
* **Phase saving.** On backtracking, each variable remembers its last value.
  Before a variable has been assigned for the first time, it is tried false.
* **Learned clause deletion.** The first deletion happens after 2000
  conflicts. The interval then grows by 300 each time. Each deletion removes
  about half of the learned clauses, preferring those with the highest LBD
  and then the oldest. Clauses with LBD ≤ 2 are never deleted, nor are
  clauses that are currently the reason for an assignment.

**Proofs.** With `--proof FILE`, every learned clause is written to `FILE` as
soon as it is learned, in the order learned. That includes learned unit
clauses. Every deleted learned clause is written as a `d` line. An
unsatisfiable run ends with `0`. Original clauses are never deleted in the
proof.

**Output.** The output follows the SAT Competition format:
* `s SATISFIABLE`, then `v` lines with 20 literals per line, then `v 0`;
  exit code 10.
* `s UNSATISFIABLE`; exit code 20.
* A file that cannot be read or parsed gives `s UNKNOWN` and exit code 1.

**Self-check.** Before printing SAT, the solver checks its model against the
parsed clauses. If that check failed it would print `s UNKNOWN` instead of a
wrong answer. This has never happened in any test.

## How the answers were checked

### The checkers

**`check.py`**
* It has its own DIMACS reader, written separately from the solver's. The
  reader is stricter: it needs a `p cnf` header, accepts only well-formed
  integers, and warns about inconsistencies.
* It requires exactly one `s` line, and `v` lines that end with a single `0`.
* The model must give exactly one value to every variable 1..n. It is
  rejected if any value is missing, repeated, contradictory or out of range.
* The model must satisfy every clause exactly as written in the file,
  including duplicate literals and tautologies.

**`drat_check.py`** checks every lemma in order. Each lemma must be RUP with
respect to the original clauses plus the earlier lemmas that have not been
deleted. RUP means: assume every literal of the lemma is false, run unit
propagation, and a conflict must follow. The proof is accepted when an empty
clause passes this test. Details:

* **Watched literals, double-checked.** Propagation uses two watched literals
  so the checker is fast enough. Each step records the clause that caused it.
  Before a lemma is accepted, a separate validator of about 25 lines re-checks
  every recorded step:
  * the implied literal belongs to its reason clause;
  * that clause is live;
  * every other literal of the clause was false earlier on the trail;
  * the conflict clause is entirely false.

  So a bug in the watched-literal code can make the checker reject a good
  proof. It cannot make it accept a lemma that is not RUP.
* **Deletions.** A deleted clause stops taking part in propagation. Literals
  that were derived at the top level are kept even if their reason clause is
  deleted later. drat-trim does the same by default. This is sound when every
  lemma is RUP: every clause ever added follows from the formula, so every
  literal derived from them does too. A deletion of a clause that is not
  present is ignored and counted.
* **Malformed or partial proofs.** A malformed proof line, a non-text file or
  a proof without an empty clause is rejected. Lines after the first empty
  clause are not read.
* **RAT lemmas** are not supported. A CDCL solver like this one does not
  produce them.

### The tests (`python3 tests/run_tests.py`, 33 tests, about 40 s)

**Random formulas against brute force (`test_random.py`).** About 3,300
random formulas with 1–12 variables are compared with brute-force search over
all 2^n assignments. The search uses bit masks and shares no code with
anything else. The formulas are:
* 1,500 with mixed clause lengths 1–5;
* 1,000 uniform 3-CNF at ratios 3–6;
* 400 4-CNF;
* 400 that include empty clauses and unit clauses.

Some clauses deliberately contain duplicate literals or tautologies. Every
answer is also certified: models by `check.py`, UNSAT answers by
`drat_check.py` on the proof. Each family must produce a reasonable number of
both SAT and UNSAT answers, so the test cannot pass trivially.

Two more parts of `test_random.py`:
* 120 formulas go through the real command line. That tests the exit codes,
  the output format (checked by running `check.py` as a program) and the
  proof file.
* 150 random 3-CNF formulas with 20–80 variables are too big for brute force.
  Their answers are accepted only with a certificate.

Seeds are fixed. `TEST_SEED=<n>` gives other formulas and `TEST_SCALE=<k>`
gives k times as many. I also ran the random tests once with
`TEST_SEED=777 TEST_SCALE=10`: about 35,000 formulas, all passed.

**Known answers (`test_structured.py`).**
* Pigeonhole PHP(n+1, n) for n ≤ 7 (UNSAT) and PHP(n, n) (SAT).
* n-queens for n = 1..20 (UNSAT exactly for n = 2, 3).
* Graph colouring: odd and even cycles with 2 colours, K_n with n−1 and n
  colours, and the Petersen graph with 2 and 3 colours.
* 120 random XOR systems, decided by Gaussian elimination.
* 60 random 2-SAT formulas with up to 400 variables, decided by strongly
  connected components.
* 80 random Horn formulas with up to 300 variables, decided by forward
  chaining.
* 25 planted 3-SAT formulas with up to 300 variables (SAT by construction).

The XOR, 2-SAT and Horn deciders are written in the tests and are
independent of the solver.

**Command-line edge cases.** These go through the real command line, and
`check.py` and `drat_check.py` verify the output:
* the empty formula (`p cnf 0 0`, which gives `v 0`) and formulas with no
  clauses;
* an empty clause;
* complementary unit clauses;
* unused variables, which must still get values;
* comments between and inside clause lines, and `%` end markers;
* a missing final `0`;
* duplicate literals and tautologies;
* variables beyond the header;
* both `--proof F` and `--proof=F`.

Another test copies the same formula under different file names, including
`n050_00.cnf`, and checks that the output is byte-for-byte identical. The
solver never reads `bench/answers.csv`; only the tests do.

**`bench/` (`test_bench.py`).** Each formula is run through the command line
with `--proof`. The answer must match `answers.csv`, and the model or the
proof must be verified. Each formula must take under 60 s.

**Tests of the checkers (`test_checkers.py`).** A checker that accepts
everything would make all of the above worthless, so the checkers are tested
too:
* **Model checker.** On 3,000 random formula and assignment pairs, it must
  agree with direct evaluation. Hand-written incomplete, duplicate,
  contradictory and out-of-range models must be rejected, as must malformed
  outputs.
* **Parser agreement.** The solver's reader and `check.py`'s reader must read
  the same clauses from 300 randomly laid-out files. That includes clauses
  split across lines, comments in between and empty clauses.
* **Hand-written DRAT cases.**
  * The checker must reject:
    * an empty clause that is implied but not RUP;
    * a lemma that is not implied;
    * a missing empty clause;
    * deletions that remove the clauses a lemma needs;
    * a proof for a satisfiable formula;
    * malformed lines.
  * It must accept:
    * a formula that already contains the empty clause;
    * complementary units;
    * tautological lemmas.
* **Soundness.** For 400 satisfiable formulas, a proof is built from the
  solver's own learned clauses plus random clauses plus a final `0`. Every
  one of these proofs must be rejected.
* **Comparison with a naive checker.** 1,200 mutated proofs of 150
  unsatisfiable formulas are checked by `drat_check.py` and by a naive
  checker in `tests/common.py`. The naive checker redoes unit propagation from
  scratch for each lemma by scanning all clauses. The mutations are:
  * a lemma dropped;
  * a literal flipped;
  * a literal dropped;
  * a random lemma inserted;
  * an original clause deleted;
  * two lemmas swapped;
  * the final `0` dropped;
  * a lemma deleted.

  Without deletions, both checkers must give exactly the same verdict. With
  deletions, `drat_check.py` must accept whenever the naive checker that
  honours deletions accepts. It must never accept when the naive checker that
  ignores deletions rejects. Both directions are asserted.

**Mutation check (`python3 tests/mutation_check.py`, several minutes).** This
plants 17 deliberate bugs, one at a time, in a copy of `solver.py`, and runs
the random, structured and bench tests against each copy. All 17 are caught.
The bugs are:
* a wrong watch replacement;
* watchers lost on conflict;
* the negation of a propagated literal left unset;
* the asserting literal not negated;
* an off-by-one in the current-level test;
* backjumping one level too far;
* minimisation through decision literals;
* deletion of locked clauses;
* learned units missing from the proof;
* a bogus proof line;
* duplicates taken for tautologies;
* an empty clause ignored;
* conflicting units not detected;
* assigned variables picked for decisions;
* a negated model;
* a dropped last clause;
* missing model values.

Some of these are caught only by the proof check. Two examples: "locked
clauses may be deleted" and "bogus proof line" are caught on PHP(8, 7).

### What the checks cover and what they do not

* **SAT answers** are fully certified, provided `check.py` reads the formula
  correctly. Its reader is separate from the solver's. The two are
  cross-tested on many layouts, and the reader is small enough to read in a
  few minutes.
* **UNSAT answers** are certified by RUP proof checking. The trust rests on
  `drat_check.py` and the reader in `check.py`. The checker itself is
  checked by the validator design, by the hand-written cases, by the
  soundness test and by the comparison with the naive checker.
* **No external checker.** I wanted to cross-check the proofs with the
  reference checker `drat-trim` as well. Building and running external code
  was not permitted in my environment, so this was not done.
* **Brute force** covers only formulas with at most 12 variables. Larger
  formulas rely on certificates, on families with known answers, and on
  `bench/answers.csv`.
* **What is certified is the answer, not the run.** The model and proof
  checks show that a given answer is correct. They do not show that the
  solver always terminates, or that it is fast on formulas unlike the
  tested ones.
* **Proof checking is forward only.** Every lemma is checked, including ones
  that are not needed for the refutation. There is no backward or core-first
  mode, so checking takes about 1–2× the solving time.
* **Not tested:**
  * binary DRAT;
  * inputs with millions of clauses;
  * running out of memory;
  * Python versions older than 3.11. Python 3.7 or later should work,
    because the code relies on dicts keeping insertion order, but this was
    not tried.

## Results on `bench/`

Measurement conditions:
* Run with `python3 tests/bench_report.py --repeat 3`.
* Each formula was run 3 times as `python3 solver.py FORMULA`, one process at
  a time, and the fastest run is reported.
* Times are wall-clock times of the whole process, so they include Python
  start-up of about 0.015 s.
* The machine is a cloud container: Intel Xeon at 2.8 GHz, Python 3.13.17.
  A laptop should be similar.
* The "with --proof" column is one run that writes the proof.
* "proof check" is the time `drat_check.py` takes to verify that proof.

| size | formulas | SAT/UNSAT | solved | correct | certified | mean time | max time | mean conflicts | max conflicts | max time with --proof | max proof check |
|---|---|---|---|---|---|---|---|---|---|---|---|
| n=50 | 20 | 12/8 | 20 | 20 | 20 | 0.03 s | 0.03 s | 48 | 122 | 0.05 s | 0.01 s |
| n=75 | 20 | 10/10 | 20 | 20 | 20 | 0.03 s | 0.04 s | 143 | 326 | 0.07 s | 0.03 s |
| n=100 | 20 | 10/10 | 20 | 20 | 20 | 0.05 s | 0.07 s | 395 | 609 | 0.09 s | 0.08 s |
| n=125 | 10 | 5/5 | 10 | 10 | 10 | 0.09 s | 0.17 s | 665 | 1321 | 0.17 s | 0.22 s |
| n=150 | 10 | 6/4 | 10 | 10 | 10 | 0.33 s | 0.90 s | 2039 | 5716 | 1.02 s | 1.71 s |
| all | 80 | 43/37 | 80 | 80 | 80 | 0.08 s | 0.90 s | 484 | 5716 | 1.02 s | 1.71 s |

The slowest formula is `n150_06.cnf` (UNSAT, 5,716 conflicts). Its proof has
about 5,700 lemmas and about 2,500 deletions.

### Beyond `bench/`: larger random 3-SAT at ratio 4.26

These formulas were generated with a fixed seed by
`python3 tests/scaling_report.py 150,175,200,225,250 8`. Times are CPU time
of the solve call only. Every answer was certified.

| n | formulas | SAT/UNSAT | certified | mean time | max time | mean conflicts | max conflicts |
|---|---|---|---|---|---|---|---|
| 150 | 8 | 6/2 | 8 | 0.18 s | 0.38 s | 1495 | 3054 |
| 175 | 8 | 5/3 | 8 | 0.66 s | 2.04 s | 3607 | 10112 |
| 200 | 8 | 4/4 | 8 | 4.01 s | 7.78 s | 14436 | 25798 |
| 225 | 8 | 6/2 | 8 | 9.91 s | 28.22 s | 26509 | 66539 |
| 250 | 8 | 4/4 | 8 | 55.82 s | 161.10 s | 91889 | 210205 |

Up to n = 225 every formula takes under 30 s. At n = 250, 2 of the 8
formulas take longer than 60 s: one SAT formula takes 161 s and one UNSAT
formula takes 93 s. Two more UNSAT formulas take 55 s and 58 s.

## What does not work, was not checked, or I am unsure about

* **Larger hard random formulas.** Random 3-SAT near the threshold grows
  exponentially harder with n. Up to n ≈ 225 the solver stays within the
  60 s limit. At n = 250 it does not reliably: in the table above, 2 of 8
  formulas took 93 s and 161 s. In an earlier experiment, one UNSAT formula
  needed 164,000 conflicts and 120 s. Hard combinatorial formulas are also
  slow: PHP(9, 8) takes about 23 s.
* **Speed of the language.** The solver runs at roughly 1,500–6,000
  conflicts per second, depending on formula size, and propagation is
  70–75% of the time. I tried two rewrites of the propagation loop:
  iterating with `for`/`enumerate` while building new watch lists, and
  avoiding the watch swap. Neither was faster on Python 3.13, so I kept the
  simpler original. Formulas with very long trails are
  slow, because each conflict re-propagates many literals. For example, a
  satisfiable planted 3-SAT formula with 5,000 variables at ratio 3.5 takes
  about 45 s.
* **Tuning.** The parameters are MiniSat/Glucose-style defaults. I tried
  other values on fixed n = 200–210 random formulas, comparing conflict
  counts:
  * Luby units of 256 and 512;
  * VSIDS decay of 0.90 and 0.99;
  * later or no clause deletion;
  * keeping clauses up to LBD 3.

  Luby 512 needed about 9% fewer conflicts on random UNSAT formulas. That is
  smaller than the variation between instances, and it may hurt on
  structured formulas, so I kept 100. Wall-clock comparisons made with 4
  processes in parallel varied by up to about 20% between identical runs, so
  I did not rely on them.
* **No time limit.** The solver has no timeout or memory limit of its own. On
  a formula too hard for it, it simply keeps running.
* **Proofs of SAT runs.** When `--proof` is given and the formula turns out
  to be satisfiable, the file is left with the lemmas learned so far and no
  empty clause.
* **What the proof checker accepts.** It keeps top-level literals whose
  reason clause has been deleted (see above). This is standard and sound for
  RUP, but it is weaker than a checker that honours every deletion exactly.
  It also stops at the first empty clause and ignores everything after it.

## Decisions made without asking

* **Input.** Lenient input in the solver, stricter input in the checkers.
  The solver accepts:
  * no header;
  * variables beyond the header, with the variable count taken as the
    maximum;
  * a missing final `0`;
  * `%` as end of input (SATLIB files).

  `check.py` needs a header but accepts the other cases with a warning, and
  reads them the same way as the solver.
* **Errors.** An unreadable or unparsable formula gives `s UNKNOWN` and exit
  code 1. The task does not specify this case.
* **Values for every variable.** Every variable 1..n gets a value, including
  variables that appear in no clause. `check.py` insists on this, as the
  task asks.
* **`v` lines** hold 20 literals per line, with the terminating `0` on its
  own `v 0` line.
* **Proof format.** Text DRAT, not binary. Deletions of learned clauses are
  included. Original clauses are never deleted. A formula with an empty
  clause, or one found inconsistent at level 0, gets the proof `0`.
* **Extra options.** `-v` prints one `c` statistics line. `--proof=FILE` is
  accepted besides `--proof FILE`.
* **Defensive model check** before answering SAT, as described above.
* **Watched-literal schemes.** The solver uses plain watched literals for
  every clause, with no special binary or ternary handling, so that it
  clearly follows the two-watched-literal scheme the task asks for. Ternary
  occurrence lists might be faster on random 3-SAT, but I did not use them
  for this reason.
* **Checker design.** The RUP checker uses watched literals for speed, and a
  separate simple validator so that its speed does not cost trust. Instead of
  `drat-trim`, which I could not run, I compared it with a naive
  scan-all-clauses checker.
* **Test-only helpers.** The tests use only the standard library.
  `tests/common.py` can load a different solver file (`SOLVER_UNDER_TEST`).
  This is only for the mutation check.
* **Task text.** `TASK.md` was left unchanged and nothing in `bench/` was
  modified.
