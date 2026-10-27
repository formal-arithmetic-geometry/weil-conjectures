## What changed

Filled the proof of `Module.Flat.of_injective_pi_of_projective_fg_ideals` in
`Sheaf.RingTheory.SemihereditaryTorsionlessFlat`, following all three existing DAG steps.
For each finite relation, the coefficient map has a finitely generated ideal as its range.
Projectivity splits its range restriction; subtracting the splitting from the identity
produces the projection onto its kernel. Evaluating the given embedding coordinatewise
then yields the projection matrix identities required by the equational criterion.
The theorem signature, docstrings, imports, and dependency route are unchanged.

Validation: `lcompile.py` compiled the final module cleanly in 3.7 seconds, with no
errors or warnings. The delivery preflight checks the declaration axioms.

Searches with LeanFinder, Loogle (`Module.Projective, Module.Flat`), the search wrapper's
grep, and local searches in Mathlib and both library roots found no direct theorem.
The proof reuses Mathlib's projective lifting property and equational criterion.

## Proved and sorry left

Closed: `Module.Flat.of_injective_pi_of_projective_fg_ideals`
(node `lem-sfb-semihereditary-torsionless-flat`). One original hole closed.
Holes added: zero. Sorries left: none. No intermediate results split off.

## No longer needed

None. Both stated proof dependencies are used, and every original import is retained.
No modules or nodes are withdrawn; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The finite free coefficient map's range is used
as the generated ideal, avoiding a separate ideal-span surjectivity calculation.
This is the same argument as the DAG plan. No definition or statement changes,
consumer adaptations, or change records are needed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
