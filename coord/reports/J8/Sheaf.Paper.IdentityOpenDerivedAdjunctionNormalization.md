## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_adjunction_normalization`
with a proof of all seven conjuncts. The theorem statement is
unchanged. The exact-left derived adjunction is used directly; the proved generic
`exactAdjunctionTransport` establishes equality with the original transported adjunction.
The localized unit is constructed componentwise with the identical component formula.
K-injectivity uses the additive equivalence and the exact open left adjoint.
Resolution naturality gives the comparison-unit identity. Its invertibility gives the
right-derived universal property. The actual derived unit is computed through the published
localization factors, and the counit follows from its triangle identity.

Updated the normalization node's proof and proof dependencies to match this argument.
Proved private categorical helpers handle adjunction transport, the exact-left unit,
the derived pullback comparison, the unit and counit calculations, and resolution
normalization. The same local Abelian-to-preadditive priority as the restriction module
keeps the complex structures consistent. Local irreducibility attributes keep the
canonical comparison constructions folded. The two equivalent construction repairs and their
consumers are documented in `coord/changes/J8-identity-open-normalization-proof-context.md`.
No consumers or public imports changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_adjunction_normalization`
(node `lem-sfb-identity-open-derived-adjunction-normalization`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. Split off: 0.
The proof uses existing named dependency theorems; it does not claim to close their holes.

## No longer needed

Removed private proof imports:

- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`: exactness instances are already
  available through the existing public imports.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`: the unit is computed
  directly and the counit follows from the triangle identity.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: existing internal
  module resolution instances suffice.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the resolution formula
  follows directly from naturality and the existing K-injective normalization.

Removed proof dependencies `lem-kun-derived-adjoint-square-comparison` and
`lem-pc-quasi-compact-base-change`. The former is replaced by the direct actual-unit
calculation; the latter is replaced by Mathlib `QuasiCompact.of_comp` for the structural
maps over the field. Removed the obsolete top-level tool approval for
`lem-kun-derived-adjoint-square-comparison`. These are dependencies pruned from this proof;
no declaration or module is withdrawn, and no global unreachability is asserted.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The geometric base-change construction and the general
adjoint-square comparison in the planned route are unnecessary: the available hypotheses
already give quasi-compactness of the open map, and the actual derived-adjunction formulas
supply the desired identities directly. The unit route is preserved.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
