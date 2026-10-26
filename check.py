#!/usr/bin/env python3
"""Independent checker for SAT solver answers.

Usage:
    python3 check.py FORMULA.cnf SOLVER_OUTPUT [--proof PROOF.drat]

SOLVER_OUTPUT is the text the solver printed ("-" reads standard input).

* "s SATISFIABLE": the "v" lines must give exactly one value to every
  variable of the formula, end with 0, and satisfy every clause.
* "s UNSATISFIABLE": verified only if --proof is given, by the RUP checker
  in drat_check.py.  Without a proof the claim is reported as unverified.

Exit code: 0 verified, 1 rejected (wrong or malformed answer), 2 unverified
(UNSAT claim without a proof).

This file shares no code with solver.py.  It works with signed DIMACS
literals throughout and parses the formula with its own reader.
"""

import re
import sys

_INT = re.compile(r'-?[0-9]+\Z')
_NAT = re.compile(r'[0-9]+\Z')


class FormatError(Exception):
    pass


def read_cnf_text(text):
    """Parse DIMACS CNF.  Returns (num_vars, clauses, warnings).

    clauses is a list of lists of non-zero ints, exactly as written in the
    file (duplicates and tautologies are kept; the checkers handle them).
    num_vars is the header value, raised to the largest variable that occurs
    (with a warning).  A clause count that differs from the header and a
    final clause without its terminating 0 are accepted with a warning.
    A line starting with "%" ends the formula (SATLIB convention).
    """
    warnings = []
    header = None
    clauses = []
    pending = []
    max_var = 0
    for lineno, raw in enumerate(text.split('\n'), 1):
        line = raw.strip()
        if line == '' or line.startswith('c'):
            continue
        if line.startswith('%'):
            break
        if line.startswith('p'):
            fields = line.split()
            if header is not None:
                raise FormatError("line %d: second header" % lineno)
            if len(fields) != 4 or fields[0] != 'p' or fields[1] != 'cnf':
                raise FormatError("line %d: bad header %r" % (lineno, raw))
            if not (_NAT.match(fields[2]) and _NAT.match(fields[3])):
                raise FormatError("line %d: bad header %r" % (lineno, raw))
            header = (int(fields[2]), int(fields[3]))
            continue
        if header is None:
            raise FormatError("line %d: clause before the header" % lineno)
        for word in line.split():
            if not _INT.match(word):
                raise FormatError("line %d: bad literal %r" % (lineno, word))
            lit = int(word)
            if lit == 0:
                clauses.append(pending)
                pending = []
            else:
                pending.append(lit)
                if abs(lit) > max_var:
                    max_var = abs(lit)
    if header is None:
        raise FormatError("no 'p cnf' header")
    if pending:
        warnings.append("last clause has no terminating 0")
        clauses.append(pending)
    num_vars, num_clauses = header
    if max_var > num_vars:
        warnings.append("variable %d exceeds the header's %d"
                        % (max_var, num_vars))
        num_vars = max_var
    if len(clauses) != num_clauses:
        warnings.append("header says %d clauses, found %d"
                        % (num_clauses, len(clauses)))
    return num_vars, clauses, warnings


def read_cnf(path):
    with open(path, 'rb') as f:
        data = f.read()
    try:
        text = data.decode('ascii')
    except UnicodeDecodeError:
        raise FormatError("formula is not ASCII text")
    return read_cnf_text(text)


def parse_output(text):
    """Parse solver output.  Returns (status, values).

    status is 'SATISFIABLE', 'UNSATISFIABLE' or 'UNKNOWN'; values is the
    list of literals from the "v" lines without the final 0 (None if there
    are no "v" lines).
    """
    status = None
    values = None
    ended = False
    for lineno, raw in enumerate(text.split('\n'), 1):
        line = raw.strip()
        if line == '' or line.startswith('c'):
            continue
        kind, _, rest = line.partition(' ')
        if kind == 's':
            if status is not None:
                raise FormatError("more than one 's' line")
            status = rest.strip()
            if status not in ('SATISFIABLE', 'UNSATISFIABLE', 'UNKNOWN'):
                raise FormatError("unknown status %r" % status)
        elif kind == 'v':
            if values is None:
                values = []
            for word in rest.split():
                if ended:
                    raise FormatError("literal after the terminating 0")
                if not _INT.match(word):
                    raise FormatError("bad value literal %r" % word)
                lit = int(word)
                if lit == 0:
                    ended = True
                else:
                    values.append(lit)
        else:
            raise FormatError("line %d: unexpected line %r" % (lineno, raw))
    if status is None:
        raise FormatError("no 's' line")
    if values is not None and not ended:
        raise FormatError("'v' lines do not end with 0")
    return status, values


def check_model(num_vars, clauses, values):
    """Return None if `values` is a full assignment satisfying every clause,
    otherwise a string describing the first problem found."""
    if values is None:
        return "SATISFIABLE without 'v' lines"
    assignment = {}
    for lit in values:
        var = abs(lit)
        if var > num_vars:
            return "value for unknown variable %d" % var
        if var in assignment:
            return "variable %d is given a value twice" % var
        assignment[var] = lit > 0
    for var in range(1, num_vars + 1):
        if var not in assignment:
            return "variable %d has no value" % var
    for index, clause in enumerate(clauses):
        if not any(assignment[abs(lit)] == (lit > 0) for lit in clause):
            return "clause %d (%s) is falsified" % (
                index + 1, " ".join(map(str, clause)))
    return None


def main(argv):
    args = list(argv[1:])
    proof = None
    if '--proof' in args:
        i = args.index('--proof')
        if i + 1 >= len(args):
            print("usage: check.py FORMULA OUTPUT [--proof PROOF]")
            return 1
        proof = args[i + 1]
        del args[i:i + 2]
    if len(args) != 2:
        print("usage: check.py FORMULA OUTPUT [--proof PROOF]")
        return 1
    try:
        num_vars, clauses, warnings = read_cnf(args[0])
        for w in warnings:
            print("c warning: " + w)
        if args[1] == '-':
            out_text = sys.stdin.read()
        else:
            with open(args[1]) as f:
                out_text = f.read()
        status, values = parse_output(out_text)
    except (OSError, FormatError) as e:
        print("REJECTED: %s" % e)
        return 1
    if status == 'SATISFIABLE':
        problem = check_model(num_vars, clauses, values)
        if problem:
            print("REJECTED: %s" % problem)
            return 1
        print("VERIFIED: satisfying assignment checked against %d clauses"
              % len(clauses))
        return 0
    if values is not None:
        print("REJECTED: 'v' lines with status %s" % status)
        return 1
    if status == 'UNKNOWN':
        print("UNVERIFIED: solver answered UNKNOWN")
        return 2
    if proof is None:
        print("UNVERIFIED: UNSATISFIABLE claimed, no proof given")
        return 2
    import drat_check
    ok, message = drat_check.check_proof_file(num_vars, clauses, proof)
    if ok:
        print("VERIFIED: " + message)
        return 0
    print("REJECTED: " + message)
    return 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
