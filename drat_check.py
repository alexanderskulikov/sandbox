#!/usr/bin/env python3
"""Forward RUP checker for DRAT proofs (text format).

Usage:
    python3 drat_check.py FORMULA.cnf PROOF.drat

Exit code 0 if the proof is verified, 1 otherwise.

What is checked
---------------
The proof is read line by line.  A line "l1 ... lk 0" is a lemma; a line
"d l1 ... lk 0" deletes a clause.  Every lemma, in order, must be RUP
(reverse unit propagation) with respect to the original clauses plus the
earlier lemmas that have not been deleted: assigning all its literals
false and running unit propagation must produce a conflict.  The proof is
accepted when a lemma that is the empty clause passes this test.  Lines
after the first empty clause are not looked at.  RAT lemmas are not
supported (a CDCL solver without inprocessing does not produce them), so a
lemma that is RAT but not RUP is rejected.

Soundness notes
---------------
* Every accepted lemma is implied by the formula, so the formula is
  unsatisfiable once the empty clause is accepted.
* Unit propagation is done with two watched literals for speed.  Every
  propagation step is recorded with the clause that caused it, and before
  a lemma is accepted a separate, simple validator re-checks the recorded
  derivation: each implied literal must belong to its (live) reason clause
  and all other literals of that clause must have been false earlier on
  the trail, and the conflict clause must be entirely false.  So a bug in
  the watched-literal code can make the checker reject a good proof but
  cannot make it accept a lemma that is not RUP.
* Literals implied at the top level (with no lemma literals assumed) are
  kept even if their reason clause is deleted later, like drat-trim does
  by default.  This is sound for RUP-only checking because every clause
  ever added is implied by the formula.  A deletion line naming a clause
  that is not present is ignored (and counted).
* Lemmas and clauses are deduplicated; tautologies are trivially RUP and
  are not stored.

This file shares no code with solver.py; the formula is read by the parser
in check.py.
"""

import re
import sys

from check import read_cnf, FormatError

_INT = re.compile(r'-?[0-9]+\Z')


def parse_proof(text):
    """Returns a list of (line_number, is_deletion, literals)."""
    steps = []
    for lineno, raw in enumerate(text.split('\n'), 1):
        words = raw.split()
        if not words or words[0].startswith('c'):
            continue
        deletion = words[0] == 'd'
        if deletion:
            words = words[1:]
        if not words or words[-1] != '0':
            raise FormatError("proof line %d does not end with 0" % lineno)
        lits = []
        for w in words[:-1]:
            if not _INT.match(w) or int(w) == 0:
                raise FormatError("proof line %d: bad literal %r"
                                  % (lineno, w))
            lits.append(int(w))
        steps.append((lineno, deletion, lits))
    return steps


class RupChecker:
    """Clause database with a persistent top-level assignment.

    Literals are signed ints.  value and watch are lists of length 2N+1
    indexed directly by the signed literal (Python's negative indexing puts
    -v at position 2N+1-v, which never collides with 1..N).
    value[l] is 1 if l is true, -1 if false, 0 if unassigned.
    """

    def __init__(self, num_vars):
        n = num_vars
        self.value = [0] * (2 * n + 1)
        self.watch = [[] for _ in range(2 * n + 1)]
        self.pos = [0] * (n + 1)      # trail position of each assigned var
        self.trail = []               # assigned literals, in order
        self.why = []                 # reason clause id per trail entry, -1
                                      # for an assumed (negated lemma) literal
        self.clauses = []             # literal lists; [0], [1] are watched
        self.frozen = []              # immutable copies for validation
        self.alive = []
        self.index = {}               # sorted literal tuple -> clause ids
        self.inconsistent = False     # top-level propagation found conflict

    # -- assignment and propagation ------------------------------------
    def _set(self, lit, reason):
        self.value[lit] = 1
        self.value[-lit] = -1
        self.pos[abs(lit)] = len(self.trail)
        self.trail.append(lit)
        self.why.append(reason)

    def _propagate(self, start):
        """Propagate the trail from position start.  Returns the id of a
        conflicting clause, or None."""
        value = self.value
        watch = self.watch
        clauses = self.clauses
        alive = self.alive
        trail = self.trail
        i = start
        while i < len(trail):
            false_lit = -trail[i]
            i += 1
            wl = watch[false_lit]
            keep = 0
            k = 0
            n = len(wl)
            while k < n:
                cid = wl[k]
                k += 1
                if not alive[cid]:
                    continue                  # drop deleted clauses lazily
                c = clauses[cid]
                if c[0] == false_lit:
                    c[0] = c[1]
                    c[1] = false_lit
                if c[1] != false_lit:
                    raise AssertionError("watch lists are corrupt")
                other = c[0]
                if value[other] == 1:
                    wl[keep] = cid
                    keep += 1
                    continue
                for m in range(2, len(c)):
                    lit = c[m]
                    if value[lit] != -1:
                        c[1] = lit
                        c[m] = false_lit
                        watch[lit].append(cid)
                        break
                else:
                    wl[keep] = cid
                    keep += 1
                    if value[other] == -1:
                        while k < n:
                            wl[keep] = wl[k]
                            keep += 1
                            k += 1
                        del wl[keep:]
                        return cid
                    self._set(other, cid)
            del wl[keep:]
        return None

    def _validate(self, start, conflict, assumed):
        """Independently re-check trail[start:] and the conflict clause."""
        value = self.value
        pos = self.pos
        trail = self.trail
        for t in range(start, len(trail)):
            lit = trail[t]
            r = self.why[t]
            if r < 0:
                if -lit not in assumed:
                    return False
                continue
            cl = self.frozen[r]
            if not self.alive[r] or lit not in cl:
                return False
            for m in cl:
                if m != lit and not (value[m] == -1 and pos[abs(m)] < t):
                    return False
        if conflict is not None:
            if not self.alive[conflict]:
                return False
            for m in self.frozen[conflict]:
                if value[m] != -1:
                    return False
        return True

    def _undo(self, length):
        value = self.value
        for lit in self.trail[length:]:
            value[lit] = 0
            value[-lit] = 0
        del self.trail[length:]
        del self.why[length:]

    # -- clause database -----------------------------------------------
    def add(self, lits):
        """Add a clause (original or verified lemma) and propagate at the
        top level."""
        uniq = list(dict.fromkeys(lits))
        if any(-l in uniq for l in uniq):
            return                                      # tautology
        cid = len(self.clauses)
        self.clauses.append(uniq)
        self.frozen.append(frozenset(uniq))
        self.alive.append(True)
        self.index.setdefault(tuple(sorted(uniq)), []).append(cid)
        if self.inconsistent:
            return
        value = self.value
        uniq.sort(key=lambda l: value[l] == -1)         # non-false first
        if len(uniq) >= 2:
            self.watch[uniq[0]].append(cid)
            self.watch[uniq[1]].append(cid)
        if not uniq or value[uniq[0]] == -1:
            # every literal is false at the top level
            if not self._validate(len(self.trail), cid, ()):
                raise AssertionError("top-level conflict not validated")
            self.inconsistent = True
            return
        if value[uniq[0]] == 0 and (len(uniq) == 1 or value[uniq[1]] == -1):
            start = len(self.trail)
            self._set(uniq[0], cid)
            confl = self._propagate(start)
            if not self._validate(start, confl, ()):
                raise AssertionError("top-level propagation not validated")
            if confl is not None:
                self.inconsistent = True

    def delete(self, lits):
        """Delete one copy of the clause; False if it is not present."""
        key = tuple(sorted(set(lits)))
        ids = self.index.get(key)
        while ids:
            cid = ids.pop()
            if self.alive[cid]:
                self.alive[cid] = False
                return True
        return False

    def is_rup(self, lits):
        if self.inconsistent:
            return True
        base = len(self.trail)
        assumed = set(lits)
        confl = None
        trivially = False
        for l in assumed:
            v = self.value[-l]
            if v == 0:
                self._set(-l, -1)
            elif v == -1:
                trivially = True       # l is already true: -l contradicts
                break
        if not trivially:
            confl = self._propagate(base)
        ok = (trivially or confl is not None) and \
            self._validate(base, confl, assumed)
        if (trivially or confl is not None) and not ok:
            self._undo(base)
            raise AssertionError("RUP derivation not validated")
        self._undo(base)
        return ok


def check_proof(num_vars, clauses, proof_text):
    """Returns (ok, message)."""
    try:
        steps = parse_proof(proof_text)
    except FormatError as e:
        return False, str(e)
    n = num_vars
    for _, _, lits in steps:
        for l in lits:
            if abs(l) > n:
                n = abs(l)
    chk = RupChecker(n)
    for c in clauses:
        chk.add(c)
    lemmas = deletions = ignored = 0
    for lineno, deletion, lits in steps:
        if deletion:
            deletions += 1
            if not chk.delete(lits):
                ignored += 1
            continue
        lemmas += 1
        try:
            ok = chk.is_rup(lits)
        except AssertionError as e:
            return False, "internal checker error at proof line %d: %s" % (
                lineno, e)
        if not ok:
            return False, "lemma at proof line %d is not RUP: %s 0" % (
                lineno, " ".join(map(str, lits)))
        if not lits:
            return True, ("empty clause derived at proof line %d; %d lemmas "
                          "are RUP; %d deletions (%d ignored)"
                          % (lineno, lemmas, deletions, ignored))
        try:
            chk.add(lits)
        except AssertionError as e:
            return False, "internal checker error at proof line %d: %s" % (
                lineno, e)
    return False, ("proof has no empty clause (%d lemmas were RUP)"
                   % lemmas)


def check_proof_file(num_vars, clauses, path):
    try:
        with open(path, 'rb') as f:
            data = f.read()
        text = data.decode('ascii')
    except OSError as e:
        return False, "cannot read proof: %s" % e
    except UnicodeDecodeError:
        return False, "proof is not a text DRAT file"
    return check_proof(num_vars, clauses, text)


def main(argv):
    if len(argv) != 3:
        print("usage: drat_check.py FORMULA.cnf PROOF.drat")
        return 1
    try:
        num_vars, clauses, warnings = read_cnf(argv[1])
    except (OSError, FormatError) as e:
        print("s NOT VERIFIED: cannot read formula: %s" % e)
        return 1
    for w in warnings:
        print("c warning: " + w)
    ok, message = check_proof_file(num_vars, clauses, argv[2])
    print("c " + message)
    print("s VERIFIED" if ok else "s NOT VERIFIED")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
