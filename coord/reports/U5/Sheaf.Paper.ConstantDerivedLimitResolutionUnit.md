## What changed

Proved `AlgebraicGeometry.Scheme.constantDerivedLimitResolutionUnit` without
changing its statement. The natural chain map is the ordinary constant/limit
adjunction unit followed by inverse limit of the resolution map. Its projections
are computed using `limMap_π` and `limit.lift_π`; degreewise joint monicity proves
uniqueness. Naturality uses the two existing natural transformations.

The witness is an explicit private definition, `resolutionUnitMap`, with a proved
`resolutionUnitMap_app` equation. Its irreducible attribute prevents repeated
unfolding of the naturality proof during kernel checking; all computations use
this application API. No new public mathematical definition is introduced.

A proved private helper, `derivedUnit_factorization`, specializes Mathlib's
`Adjunction.derivedη_fac_app` to the existing exact-left/right-derived adjunction.
`Adjunction.derived_unit` avoids unfolding the full derived adjunction construction.
It makes the identity comparison components explicit. Applying naturality of
`rightDerivedFunctorUnit` to the resolution map gives the required resolution
formula. The last clause is naturality of the specified derived adjunction unit.

Updated the item's node proof to match these six steps. No new node, public definition,
public declaration, or statement change is introduced. The unit route is retained.

Validation: the complete module compiled through `lcompile.py` with zero errors
and zero warnings in 35.1 seconds. The original public theorem statement is
byte-identical, and the delivered Lean contains zero `sorry` tokens.
The public-import cleanup is recorded in
`coord/changes/constant-derived-limit-resolution-unit-imports.md`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.constantDerivedLimitResolutionUnit`
(node `lem-cbc-constant-derived-limit-resolution-unit`).

Added zero holes; zero remain in the delivered Lean file. The private helpers
`resolutionUnitMap_app` and `derivedUnit_factorization` are proved, and
`resolutionUnitMap` is constructed with complete naturality data. This is a proof from the existing library
and Mathlib declarations, not a decomposition into new unfinished statements.

The compatibility identity holds for every functor J and natural map into J.
Thus the existing quasi-isomorphism and K-injectivity hypotheses can be cleared
in this proof; they remain verbatim in the theorem statement.

## No longer needed

Removed the unused `Sheaf.Paper.PbcQbarCompletedPullback` public import. The
common-stage Qbar pullback and its unfinished constructibility results play no
role in this integral constant-tower unit. This does not withdraw that module
or its declarations from other consumers.

Removed the following redundant explicit imports, whose required infrastructure
is already publicly available through `Sheaf.Paper.CompletedPullback`:

- `Sheaf.CategoryTheory.RingedSiteModules`;
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`;
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
- `Mathlib.CategoryTheory.Functor.OfSequence`;
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`;
- `Mathlib.CategoryTheory.Localization.Predicate`;
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`.

The proof does not need a second explicit localization descent using
`Localization.liftNatTrans`. Mathlib's existing derived adjunction already
supplies the descended transformation, and its factorization theorem identifies
it with the resolution map. Accordingly, removed
`lem-weil-pbc-localization-universal-property` from the node's proof dependencies.
All other stated dependencies are retained. No module is withdrawn. A downstream
search found zero current Lean importers; unfinished DAG parents still require
the item and its full original statement.

## Where the brief, the DAG or earlier work was wrong

The initial Qbar pullback import was unrelated to this theorem, as the earlier
statement review also observed. The DAG's explicit descent construction can be
realized by the existing derived adjunction and its factorization API; rebuilding
a new descent would duplicate this construction. The original statement and
projection-defined interpretation are correct and unchanged.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
