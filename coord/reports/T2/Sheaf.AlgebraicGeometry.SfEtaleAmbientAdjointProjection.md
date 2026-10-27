## What changed

Proved `AlgebraicGeometry.Etale.sfEtaleAmbientAdjointProjection` without changing its
signature or the definition `sfEtaleAmbientTensorMap`. The adjoint is obtained by
composing the existing proper derived left-adjoint instance with the exact open
extension-by-zero derived adjunction. The canonical projection component is the
proper finite-coefficient projection map followed by mapped isomorphisms, as
specified by `projectionMapOfCompactification_app_app`.

Added private proof imports of
`Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint` and
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`.
Retained the private `ProjectionFormula` import and all four public imports.
Updated the item's proof steps, proof dependencies and proof origin to this route.
No definitions, statements, source-library modules or consumers are changed.

The existing node `lem-etale-proper-derived-direct-image-adjoint` is used as a
categorical tool for the proper factor. Its statement explicitly permits arbitrary
schemes and ordinary unbounded categories; the proof uses the existing proper
projection formula and Brown theorem. Likewise the existing finite proper
projection node `lem-etale-proper-projection-formula-finite` is used as a tool.
Neither use bypasses a realized step of the item's unit
`sk-prop-sf-rf-shriek-preservation`; this item is its ambient adjunction input.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.sfEtaleAmbientAdjointProjection`
(node `lem-sf-etale-ambient-adjoint-projection`).
Added 0 holes; split off 0 statements. No textual sorry remains in the module.
The definition `AlgebraicGeometry.Etale.sfEtaleAmbientTensorMap` continues to use
this theorem to invert the projection component. Its body and type are unchanged.
This is a complete proof from already-declared library results, not a decomposition.

Validation: the item compiles alone through lcompile.py; the delivery compiler
also checks each declaration's axioms. The argument requires only a finite
commutative ring and the supplied compactification. In particular it adds no
nonzero-ring, Noetherian, boundedness or quasi-compact-open assumption.

## No longer needed

Removed the following direct private imports:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`
- `Mathlib.CategoryTheory.Triangulated.Adjunction`
- `Mathlib.CategoryTheory.Triangulated.Functor`
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums`
- `Sheaf.CategoryTheory.CoproductsOfCopowers`
- `Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint`

Removed the following direct proof dependencies; their corresponding old
`tool_uses` entries, when present, were also removed in their original order:

- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-sfb-grothendieck-k-injective`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-sp-canonical-right-derived-adjunction-shift`
- `lem-sf-triangulated-right-adjoint`
- `lem-weil-pbc-triangulated-functor-composite`
- `lem-kun-0f0g`
- `lem-kun-derived-tensor-direct-sums`
- `lem-coproducts-of-copowers`
- `lem-grothendieck-derived-brown-right-adjoint`

The open/proper adjunction composition replaces the separate copower-preservation,
naturality-at-the-unit and Brown argument in this module. These generic results
may remain dependencies of the existing proper-adjoint theorem: no source-library
declaration or globally needed node is withdrawn.

A source-import closure comparison removes these five project modules from this
item's import closure:

- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`

No module is withdrawn. Global target-closure pruning is for the ledger to compute.

## Where the brief, the DAG or earlier work was wrong

The nine-step plan repeats results that already have complete library proofs.
In particular, both proper-factor adjunction and finite proper projection exist
without Noetherian assumptions. Reusing them avoids repeating the copower glue.
The mathematical statement and unit route are unchanged.

The node `thm-amb-etale-exceptional-adjoint` still records a Noetherian signature,
although its source-library declaration is now general. This delivery instead uses
the exactly matching arbitrary-base proper-factor node and the derived open
adjunction; it does not alter that unrelated record.

The compile service intermittently selected a local mirror missing Mathlib.olean.
The supported `LCOMPILE_NO_LOCAL=1` setting sends validation through lcompile.py to
the project server, as required by the worker brief. No launcher file was changed.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
