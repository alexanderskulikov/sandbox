#!/usr/bin/env python3
"""Time the solver on bench/ and print the tables used in REPORT.md.

    python3 tests/bench_report.py [--repeat K]

Each formula is run K times (default 1) as a separate process, exactly as
"python3 solver.py FORMULA" (no proof), one at a time; the time is the
wall-clock time of the whole process, including Python start-up.  Then the
run with --proof is timed once, and the proof is checked with
drat_check.py (time also reported).
"""

import csv
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import BENCH, SOLVER, check, drat_check  # noqa: E402


def timed(cmd):
    start = time.perf_counter()
    p = subprocess.run(cmd, capture_output=True, text=True)
    return time.perf_counter() - start, p


def main():
    repeat = 1
    if '--repeat' in sys.argv:
        repeat = int(sys.argv[sys.argv.index('--repeat') + 1])
    with open(os.path.join(BENCH, 'answers.csv')) as f:
        answers = {r['file']: r['answer'] for r in csv.DictReader(f)}
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        for name in sorted(answers):
            path = os.path.join(BENCH, name)
            times = []
            for _ in range(repeat):
                t, p = timed([sys.executable, SOLVER, path])
                times.append(t)
            got = {10: 'SAT', 20: 'UNSAT'}.get(p.returncode, 'ERROR')
            proof = os.path.join(tmp, 'p.drat')
            tp, p2 = timed([sys.executable, SOLVER, path, '--proof', proof])
            n, clauses, _ = check.read_cnf(path)
            start = time.perf_counter()
            if got == 'SAT':
                status, values = check.parse_output(p.stdout)
                verified = check.check_model(n, clauses, values) is None
                lemmas = 0
            else:
                verified, _ = drat_check.check_proof_file(n, clauses, proof)
                with open(proof) as f:
                    lemmas = sum(1 for line in f if not line.startswith('d'))
            tc = time.perf_counter() - start
            stats = subprocess.run([sys.executable, SOLVER, path, '-v'],
                                   capture_output=True, text=True).stdout
            conflicts = int(stats.split('conflicts ')[1].split()[0])
            rows.append(dict(name=name, size=name.split('_')[0],
                             expected=answers[name], got=got,
                             correct=got == answers[name], verified=verified,
                             time=min(times), proof_time=tp, check_time=tc,
                             conflicts=conflicts, lemmas=lemmas))
            print('%-12s %-5s %-5s %6.2fs  proof %6.2fs  check %6.2fs  '
                  'conflicts %6d  %s' % (
                      name, answers[name], got, min(times), tp, tc,
                      conflicts, 'ok' if got == answers[name] and verified
                      else 'PROBLEM'), file=sys.stderr)

    print('| size | formulas | SAT/UNSAT | solved | correct | certified '
          '| mean time | max time | mean conflicts | max conflicts '
          '| max time with --proof | max proof check |')
    print('|---|---|---|---|---|---|---|---|---|---|---|---|')
    sizes = sorted(set(r['size'] for r in rows))
    for size in sizes + ['all']:
        rs = [r for r in rows if size in ('all', r['size'])]
        sat = sum(r['expected'] == 'SAT' for r in rs)
        solved = sum(r['got'] in ('SAT', 'UNSAT') for r in rs)
        print('| %s | %d | %d/%d | %d | %d | %d | %.2f s | %.2f s | %d | %d '
              '| %.2f s | %.2f s |' % (
                  'n=%d' % int(size[1:]) if size != 'all' else 'all',
                  len(rs), sat, len(rs) - sat, solved,
                  sum(r['correct'] for r in rs),
                  sum(r['verified'] for r in rs),
                  sum(r['time'] for r in rs) / len(rs),
                  max(r['time'] for r in rs),
                  sum(r['conflicts'] for r in rs) / len(rs),
                  max(r['conflicts'] for r in rs),
                  max(r['proof_time'] for r in rs),
                  max(r['check_time'] for r in rs)))


if __name__ == '__main__':
    main()
