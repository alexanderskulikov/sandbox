#!/usr/bin/env python3
"""Mutation check: do the tests catch bugs in the solver?

    python3 tests/mutation_check.py

Each mutant is a copy of solver.py with one deliberate bug.  The test
suite (random, structured and bench tests) is run against the mutant with
SOLVER_UNDER_TEST pointing to it; a mutant is "killed" if some test fails
(or the run times out).  Every mutant listed here changes the solver's
behaviour in a way that can produce a wrong answer, a wrong certificate or
a crash; mutants that only change performance are not included.

This is slow (several minutes) and is not part of run_tests.py.
"""

import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

MUTANTS = [
    ("replacement watch must be unassigned (ignores true literals)",
     "                    if val[lk] != -1:\n                        c[1] = lk",
     "                    if val[lk] == 0:\n                        c[1] = lk"),
    ("unvisited watchers dropped on conflict",
     "            del ws[j:i]\n",
     "            del ws[j:]\n"),
    ("negation not marked false on propagation",
     "                    val[c0] = 1\n                    val[c0 ^ 1] = -1\n",
     "                    val[c0] = 1\n"),
    ("asserting literal not negated",
     "        learnt[0] = p ^ 1\n",
     "        learnt[0] = p\n"),
    ("current-level test off by one in analysis",
     "                        if lv >= cur:\n",
     "                        if lv > cur:\n"),
    ("backjump one level too far",
     "            bt = ml\n",
     "            bt = max(0, ml - 1)\n"),
    ("minimisation ignores decision literals",
     "                    if reason[v] is not None and \\\n",
     "                    if True and \\\n"),
    ("locked clauses may be deleted",
     "            if lbd[id(c)] <= self.KEEP_LBD or self.locked(c):\n",
     "            if lbd[id(c)] <= self.KEEP_LBD:\n"),
    ("learned units not written to the proof",
     "                self.write_proof(learnt)\n",
     "                if len(learnt) > 1:\n"
     "                    self.write_proof(learnt)\n"),
    ("deletion line replaced by a bogus (shortened) lemma",
     "                self.write_proof(c, delete=True)\n",
     "                self.write_proof(c[:-1], delete=False)\n"),
    ("duplicate literal taken for a tautology",
     "                if lit ^ 1 in lits:\n",
     "                if lit in lits or lit ^ 1 in lits:\n"),
    ("empty input clause ignored",
     "                self.ok = False             # empty clause in the input\n",
     "                pass\n"),
    ("conflicting input units not detected",
     "                if v == -1:\n                    self.ok = False\n",
     "                if v == -2:\n                    self.ok = False\n"),
    ("assigned variables may be picked as decisions",
     "                if val[2 * v] == 0:\n                    return v\n",
     "                return v\n"),
    ("model printed with every value negated",
     "        return [v if val[2 * v] == 1 else -v for v in range(1, self.n + 1)]",
     "        return [-v if val[2 * v] == 1 else v for v in range(1, self.n + 1)]"),
    ("last clause without 0 dropped",
     "    if cur:\n        clauses.append(cur)\n",
     "    pass\n"),
    ("unused variables missing from the model",
     "        return [v if val[2 * v] == 1 else -v for v in range(1, self.n + 1)]",
     "        return [v if val[2 * v] == 1 else -v for v in range(1, self.n + 1)\n"
     "                if self.watches[2 * v] or self.watches[2 * v + 1]]"),
]

TESTS = ['test_random', 'test_structured', 'test_bench']


def main():
    with open(os.path.join(ROOT, 'solver.py')) as f:
        original = f.read()
    killed = 0
    with tempfile.TemporaryDirectory() as tmp:
        for i, (name, old, new) in enumerate(MUTANTS):
            if original.count(old) != 1:
                print("mutant %d (%s): pattern found %d times -- fix the "
                      "mutation list" % (i, name, original.count(old)))
                return 2
            path = os.path.join(tmp, 'solver_mutant_%d.py' % i)
            with open(path, 'w') as f:
                f.write(original.replace(old, new))
            env = dict(os.environ, SOLVER_UNDER_TEST=path)
            try:
                p = subprocess.run(
                    [sys.executable, '-m', 'unittest', '-f'] + TESTS,
                    cwd=HERE, env=env, capture_output=True, text=True,
                    timeout=600)
                failed = p.returncode != 0
                last = [l for l in p.stderr.splitlines()
                        if l.startswith(('FAIL:', 'ERROR:'))]
                detail = last[0] if last else 'all tests passed'
            except subprocess.TimeoutExpired:
                failed = True
                detail = 'timeout'
            killed += failed
            print("%-8s %-62s %s" % ('killed' if failed else 'SURVIVED',
                                      name, detail), flush=True)
    print("%d of %d mutants killed" % (killed, len(MUTANTS)))
    return 0 if killed == len(MUTANTS) else 1


if __name__ == '__main__':
    sys.exit(main())
