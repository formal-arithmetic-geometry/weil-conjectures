# FiniteClopenDerivedDecomposition proof elaboration context

## Reason

The proof dependencies provide generalized derived-category instances and large native
monoidal constructions. Unrestricted instance search and definitional equality unfold
those constructions repeatedly. Local proof contexts select the existing fixed-universe
instances and use the existing exact-functor and tensor comparison APIs instead.
All original public signatures, public imports, attributes on declarations and non-theorem
bodies are retained. No exported construction is replaced.

## Old

The original module-wide proof elaboration settings, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The original per-declaration instance exclusions and all public signatures and
non-theorem bodies are retained verbatim. Six theorem bodies were `by sorry`.

## New

The replacement module-wide proof elaboration context, verbatim:

```lean
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.RingedDerivedNative.monoidal
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

```

Private proof imports supply normalized gluing, direct tensor comparisons,
completed restriction and coefficient comparisons. Additional local reducibility
settings inside the file seal derived functors, the coefficient-ring alias and
residue fields; the coefficient alias is reopened for the final normalization
statements. Scoped proof contexts open the on-slice aliases used by the normalized
completion comparison. These settings select existing structures; no definition's
data or public signature changes. Four theorem holes are filled. The constructible
equivalences and finite restriction identification retain their original holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.ClopenCommonCompactSupport | Y3 | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same public signatures and constructions; no source adaptation. |
| Sheaf.Paper.ClopenRoosIntegralDescent | C3 | Same public signatures and constructions; no source adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | H4 | Same public signatures and constructions; no source adaptation. |

All direct consumers retain the same public declarations and definition bodies. No
consumer is edited. These proof elaboration settings do not change target meanings.
The delivery's consumer checks verify their unchanged sources against this module.

## Status

landed 20261025T205508-L-3266574 2026-10-25 (merge of deliver/J5/Sheaf.Paper.FiniteClopenDerivedDecomposition)
