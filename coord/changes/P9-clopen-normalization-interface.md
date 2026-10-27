# ClopenMonoidalDescent normalization interface extraction

## Reason

The remaining coherent-lift theorem must use the existing normalization predicates, while
its parent theorem imports that lemma. Move the interface to an acyclic shared module and
publicly reexport it. This is a logical dependency separation, not a compile-time split.
Every moved declaration keeps its name, visibility, type, attributes, and body verbatim.
The normalization predicates, native monoidal instances, localization factors, and canonical
unit therefore mean precisely what they meant before. No theorem assumption or conclusion,
and no target's meaning, changes.

## Old

In `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent`:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Mathlib.CategoryTheory.Pi.Monoidal

```

The declarations `modulesAbelian`, `restrictionLimits`, `restrictionColimits`, `hasDerived`,
`monoidal`, `symmetric`, `derivedRestriction`, `factors`, `Comparison`, `TotalNormalization`,
`ModelNormalization`, `braidedComparison`, `unitComparison`, `braidedUnit`, and `familyBraided`
(in namespace `AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent`) precede the theorem.

## New

In that item module:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleClopenMonoidalNormalization
```

The exact old public imports and all fifteen declarations, with their original statements
and definition bodies, occur in that new interface module. The item publicly reexports
it. The independently assigned new coherent-lift theorem publicly imports the interface,
and the item privately imports the coherent-lift theorem.

The only mathematical theorem newly stated is
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_model_normalization`,
attached to `lem-pur-clopen-braided-model-normalization`. It has a whole-proof `sorry` with
a full proof in words and is strictly part of the original argument. The parent proves
uniqueness, generator normalization, finite-family equivalence, and assembly itself.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent | P9 | Publicly reexports the identical interface; proves the original theorem from the remaining component step. |
| Sheaf.AlgebraicGeometry.ProEtaleClopenMonoidalNormalization | new, P9 | Holds the unchanged existing interface. |
| Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization | new, P9 | States the coherent model/unit lift using that interface. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent` reports
zero downstream modules; its `--uses ModelNormalization` reports only the item. No
existing consumer adaptation is required. The item's namespace and theorem signature
remain identical. Source-library files and target signatures are unchanged.

## Status

landed 20261025T123513-L-1875872 2026-10-25 (merge of deliver/P9/Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent)
