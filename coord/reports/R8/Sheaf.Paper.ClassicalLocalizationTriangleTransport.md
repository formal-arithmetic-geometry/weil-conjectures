## What changed

Proved `AlgebraicGeometry.ProEtale.classicalLocalizationTriangleTransport` from the existing
natural etale closed-support triangle and canonical direct-image mates. Three proved private
helpers establish invertibility, naturality, and the D+/D etale unit compatibility. The proof
constructs the specified alpha and gamma, checks the actual pro-etale unit, constructs a triangle
isomorphism using their inverses, and proves all three naturality equations, including the
boundary with its specified shift and sign.

Added the private proof import
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat` to use the existing
identification of unbounded etale adjunctions. Updated the item's node proof and proof dependencies
to this implementation. All existing declaration signatures, definition bodies, docstrings and
public imports are unchanged. No source-library file was edited.

Validation: the full delivered module compiled through `lcompile.py` in 15.6 seconds with
exit code 0 and no warnings. The three private helpers also compiled separately in 4.4 seconds.
The import-direction check permits the added proof import. Static checks confirmed unchanged
public definition bodies, theorem signature and public imports, no holes and lines at most
100 characters.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.classicalLocalizationTriangleTransport`
(node `lem-pur-classical-localization-triangle-transport`).

Holes added: 0. Holes left in the delivered Lean module: 0. No result was split off.
The three private helpers have complete proofs. Existing imported theorems are used as permitted
by stage 3; this delivery does not claim to close their transitive proof dependencies.

## No longer needed

Removed these six redundant or unused private proof imports:

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`

The first is already available through retained imports. The remaining five do not
supply a step of this proof. Specifically, removed the following six direct proof dependencies
from the node:

- `lem-cbc-open-closed-recollement` (`Sheaf.AlgebraicGeometry.OpenClosedRecollement`)
- `lem-exc-proetale-closed-exact`
  (`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`)
- `lem-weil-pbc-exact-functor-derived-functor` (`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`)
- `lem-weil-pbc-dplus-injective-representative` (Mathlib leaf)
- `lem-weil-pbc-kinjective-total-derived` (`Sheaf.CategoryTheory.KInjectiveTotalDerived`)
- `prop-weil-pbc-kinjective-resolutions-exist`
  (`Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`)

The statement already uses derived closed images, so no replacement by an underived exact
closed image is necessary. The existing `rightDerivedFunctorPlusCompatibility` supplies the
D+/D comparison, so no fresh injective or K-injective construction is necessary. These nodes
can remain necessary to other modules, including the existing comparison and support-triangle
proofs. The five obsolete `tool_uses` approvals for the removed non-Mathlib dependencies were deleted,
with the remaining approvals preserved in order. No module or declaration is withdrawn by
this packet.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and unit route required no correction. The plan's closed-image
exactness normalization and fresh injective-model construction were redundant for the present
Lean interface. The bounded-below adjunction is already defined by restricting the unbounded
one, so its required unit compatibility follows directly from
`Adjunction.map_restrictFullyFaithful_unit_app` and the existing etale adjunction comparison.
No definition repair or consumer adaptation was needed.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
