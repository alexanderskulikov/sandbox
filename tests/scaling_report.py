#!/usr/bin/env python3
"""Time the solver on random 3-SAT at clause/variable ratio 4.26 for sizes
beyond bench/ (formulas are generated with a fixed seed).

    python3 tests/scaling_report.py [SIZES] [COUNT]

e.g.  python3 tests/scaling_report.py 150,175,200,225,250 8

Each formula is solved in-process, one at a time; every answer is
certified with check.py / drat_check.py.  Times are CPU seconds of the
solve call only (no parsing, no Python start-up).
"""

import io
import sys
import time

from common import (check, drat_check, make_rng, random_kcnf, solver,
                    to_dimacs)


def main():
    sizes = [int(x) for x in (sys.argv[1] if len(sys.argv) > 1
                              else '150,175,200,225,250').split(',')]
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    print('| n | formulas | SAT/UNSAT | certified | mean time | max time '
          '| mean conflicts | max conflicts |')
    print('|---|---|---|---|---|---|---|---|')
    for n in sizes:
        rng = make_rng('scaling', n)
        rows = []
        for _ in range(count):
            clauses = random_kcnf(rng, n, int(round(4.26 * n)), 3)
            proof = io.StringIO()
            start = time.process_time()
            s = solver.Solver(n, clauses, proof)
            sat = s.solve()
            elapsed = time.process_time() - start
            nv, cl, _ = check.read_cnf_text(to_dimacs(n, clauses))
            if sat:
                ok = check.check_model(nv, cl, s.model()) is None
            else:
                ok, _ = drat_check.check_proof(nv, cl, proof.getvalue())
            rows.append((sat, ok, elapsed, s.conflicts))
            print('n=%d %s %.2fs %d conflicts %s' % (
                n, 'SAT' if sat else 'UNSAT', elapsed, s.conflicts,
                'certified' if ok else 'NOT CERTIFIED'), file=sys.stderr,
                flush=True)
        nsat = sum(r[0] for r in rows)
        print('| %d | %d | %d/%d | %d | %.2f s | %.2f s | %d | %d |' % (
            n, count, nsat, count - nsat, sum(r[1] for r in rows),
            sum(r[2] for r in rows) / count, max(r[2] for r in rows),
            sum(r[3] for r in rows) / count, max(r[3] for r in rows)),
            flush=True)


if __name__ == '__main__':
    main()
