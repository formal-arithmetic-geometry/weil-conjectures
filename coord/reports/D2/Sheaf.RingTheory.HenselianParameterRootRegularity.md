## What changed

Proved Algebra.henselian_parameter_root_regularity in
Sheaf.RingTheory.HenselianParameterRootRegularity, with every original hypothesis,
conclusion and the coordinate definition unchanged. Added proved private helpers
for exponent-reduction normal forms, the bounded monomial basis, quotient evaluation,
locality, residue and closed-fibre isomorphisms, and maximal-ideal generators.

The proof constructs all maps explicitly. It reuses the generic integral-dimension,
regular-local-domain and finite-local-henselian theorems. Updated the existing DAG
proof to record the direct normal form argument. No new module or node is needed.

Removed unused scheme public imports and the unused AdjoinRoot proof import;
added private proof imports for Finsupp linear combinations, quotient linear maps
and the coordinate-vector basis. See coord/changes/D2-henselian-parameter-root-imports.md.

## Proved and sorry left

Closed 1 of 1 original holes:
Algebra.henselian_parameter_root_regularity
(node lem-sfb-henselian-parameter-root-regularity).

Added 0 holes; split off 0 statements. There are no sorries in the delivered module.
All private helper declarations are proved. The theorem covers arbitrary positive
exponents, including n=1 and exponents divisible by the residue characteristic,
and the empty family r=0; no division by n or root of unity is used.

Single-file compilation passes without errors or warnings through lcompile.py.
The final delivery preflight checks the axioms of all delivered declarations.

## No longer needed

Removed imports:
- Mathlib.AlgebraicGeometry.ResidueField (scheme residue fields; only the local-ring
  residue field is used).
- Sheaf.AlgebraicGeometry.IsRegularScheme (scheme regularity; only the existing
  ring predicate IsRegularLocalRing is used).
- Mathlib.RingTheory.AdjoinRoot (the simultaneous quotient is handled directly).

Declared dependency no longer used:
lem-weil-pbc-monic-quotient-free. Its proposed iterated monic quotient argument
is replaced by an R-linear normal form on the simultaneous polynomial quotient,
which sends bounded monomials to the standard coordinate vectors. The dependency
is removed from this node's proof_deps. No claim is made that this generic Mathlib
leaf is unused elsewhere.

All other declared proof dependencies remain needed, including the ring portion of
def-weil-regular-scheme. No module is withdrawn and no parent dependency is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The DAG's iterated quotient route is
valid but needs comparison isomorphisms and iterated bases; the direct normal form
avoids that infrastructure. The original scheme imports were unnecessary for this
ring-theoretic statement. The unit route and all existing public signatures stay intact.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
