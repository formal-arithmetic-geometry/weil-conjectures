## What changed

Completed the four theorem proofs in
`Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitFiniteSplitting`.
All existing public declarations, signatures, structures, and public imports are unchanged.

Finite-stage morphisms are the preimages of the equivariant coset maps under the existing
`FiniteEtale.equivalenceContAction`. Their existence theorem is proved here; the choices
used in assembling the splitting therefore introduce no unproved data. The kernel of each
finite permutation action is an open normal subgroup, including for the empty fibre.

Private proved helpers establish evaluation injectivity for maps from any connected scheme,
uniqueness for maps into the specified limit, and the graph coproduct by reflecting a
bijection on the geometric fibre of a finite-etale morphism over the connected source.
The limit universal property then constructs the normalized deck automorphisms. Pullback
sections construct the comparison, and `fundamentalGroupMap_smul` proves equivariance.
The identity and composition clauses follow directly from pointed uniqueness.

Updated the node's proof and proof origin to record the direct uniqueness and graph argument.
The final module compiled on the project server in 22.5 seconds with no errors or warnings.

## Proved and sorry left

Closed all four original holes:

- `AlgebraicGeometry.Scheme.exists_pointedLimitSplitting`;
- `AlgebraicGeometry.Scheme.exists_unique_pointedLimitComparison`;
- `AlgebraicGeometry.Scheme.pointedLimitComparison_id`;
- `AlgebraicGeometry.Scheme.pointedLimitComparison_comp`.

All four realize `lem-sfb-pointed-limit-finite-splitting`.
No remaining `sorry` in the module. Zero holes added; zero statements split off.

## No longer needed

Removed the unused private import
`Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`.
The finite-etale part of `thm-galois-fundamental` is supplied by the already imported
`FiniteEtale.equivalenceContAction`, rather than the additional FLC equivalence theorem.
The DAG dependencies remain relevant: fibre functor, finite-coproduct and pullback
interfaces, fundamental-group equivalence, and fundamental-group functoriality.

A separate finite-stage coproduct calculation and its base-change transport are unnecessary:
the graph coproduct can be verified at the point of the connected limit itself. Factoring
arbitrary maps out of the limit through a finite stage is likewise unnecessary for
uniqueness. No node or module is withdrawn; no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The existing plan used longer routes for splitting and
marked-point uniqueness. The replacement proves the same assertions, including empty
fibres, and leaves the unit statement and its realized steps unchanged. No definition
repair or consumer adaptation is needed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
