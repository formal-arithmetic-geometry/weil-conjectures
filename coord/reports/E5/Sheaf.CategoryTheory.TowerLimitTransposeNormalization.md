## What changed

Proved `CategoryTheory.TowerLimitTransposeNormalization.tower_limit_transpose_normalization`
without changing its statement or any existing definition. The comparison is the conjugate of
`UnboundedExactTower.constantInterchange` under the two composite canonical derived adjunctions.
Private helpers transport the ordinary counit equations through localization, identify the
ordinary conjugate with `preservesLimitNatIso`, and establish the constant-limit unit is invertible.
The two requested Hom formulas follow from conjugation and naturality. The complete module
compiled through `lcompile.py` in 18.8 seconds, with no warnings or remaining holes.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.TowerLimitTransposeNormalization.tower_limit_transpose_normalization`
(node `lem-pur-tower-limit-transpose-normalization`). Added zero holes and split off zero statements.
All private helpers are proved. No `sorry` remains in the delivered module.

## No longer needed

The proof uses the exact adjunction already carried by `d`, so it does not need the separate
existence results `lem-pe-constant-left-module-inverse-image` or
`lem-weil-pbc-ringed-topoi-module-adjunction`. The formal mate calculation replaces the direct
resolution computation, so it does not use
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-weil-ringed-tower-pushforward-limit-comparison`,
`lem-weil-pbc-diagram-site-realization`,
`prop-pur-kinjective-resolutions-exist`,
`lem-weil-pbc-kinjective-total-derived`, or
`lem-weil-pbc-kinjective-hom-derived` as separate proof lemmas. Their mathematical
constructions occurring in the statement retain their original definitions and normalization.

Removed the following proof imports:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`

The latter Mathlib/upstream APIs remain available through the existing public imports.
No module or declaration is withdrawn. Pruning is relative to this proof; other users may
continue to require these modules.

## Where the brief, the DAG or earlier work was wrong

The seven-step plan is mathematically valid, but its calculation can be proved directly
using naturality and injectivity of adjunction transposition. This proves the representative
normalization for every complex, without choosing a common K-injective representative of
each arrow. K-injective resolutions are needed for the existing derived adjunctions and for
invertibility of the constant-limit unit. The unit-level route is preserved.

The proof-context change record is
`coord/changes/E5-tower-limit-private-proof-context.md`. It documents only private helper
contexts; there is no mathematical interface change and no forced adaptation.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
