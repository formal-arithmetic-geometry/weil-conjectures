# AlgebraicGeometry.tensorResolutionRestrictionTensorMap

## Reason

Repair the returned delivery e0bf08fe0 against the current restored module, rather than
reintroducing its duplicate definition. The current comparison-naturality compatibility
module re-exports the canonical upstream definition, but it cannot be imported alongside
`Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality`: the latter still duplicates
upstream declarations. A two-import compile reproduces this error:

```text
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTensorNaturality failed,
environment already contains 'AlgebraicGeometry.TensorResolutionTensorNaturality_localInst1'
from Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality
```

The archived TotalCoherence consumer reaches both paths through RestrictionCoherence and
TotalComponents. Normalize the unclaimed TensorNaturality companion to re-export its
upstream implementation too. Retain the current item's upstream public import, and add the
companion's public import to preserve the old explicit Sheaf tensor-naturality dependency.
Both paths then refer to the very same definitions and theorems. This repairs a reproduced
import failure; it is not merely a rebase of the earlier packet.

## Old

The current item's header:

```lean
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality
```

The companion module, verbatim:

```lean
module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionHomologyZigzag

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionTensorNaturality_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionTensorNaturality_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionTensorNaturality_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionTensorNaturality_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Composition of total tensor maps. -/
theorem tensorResolution_totalTensor_comp {X : Scheme.{u}}
    {E₁ E₂ E₃ F₁ F₂ F₃ : CochainComplex X.Modules ℤ}
    (a : E₁ ⟶ E₂) (b : F₁ ⟶ F₂) (c : E₂ ⟶ E₃) (d : F₂ ⟶ F₃) :
    HomologicalComplex.mapBifunctorMap a b (curriedTensor X.Modules) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap c d (curriedTensor X.Modules) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (a ≫ c) (b ≫ d)
        (curriedTensor X.Modules) (.up ℤ) := by
  ext i : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [HomologicalComplex.ι_mapBifunctorMap, Category.assoc,
    ← tensorHom_comp_tensorHom, whisker_exchange_assoc]

/-- A pair of chain squares induces a square on restricted total tensor complexes. -/
theorem tensorResolution_restrictedTensor_square {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    {E₁ E₂ F₁ F₂ : CochainComplex Y.Modules ℤ}
    {E₁' E₂' F₁' F₂' : CochainComplex X.Modules ℤ}
    (a : E₁ ⟶ E₂) (b : F₁ ⟶ F₂) (a' : E₁' ⟶ E₂') (b' : F₁' ⟶ F₂')
    (s₁ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E₁ ⟶ E₁')
    (s₂ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E₂ ⟶ E₂')
    (t₁ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F₁ ⟶ F₁')
    (t₂ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F₂ ⟶ F₂')
    (ha : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map a ≫ s₂ = s₁ ≫ a')
    (hb : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map b ≫ t₂ = t₁ ≫ b') :
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a b (curriedTensor Y.Modules) (.up ℤ)) ≫
      (tensorResolutionRestrictionTotalIso j E₂ F₂).hom ≫
      HomologicalComplex.mapBifunctorMap s₂ t₂ (curriedTensor X.Modules) (.up ℤ) =
    (tensorResolutionRestrictionTotalIso j E₁ F₁).hom ≫
      HomologicalComplex.mapBifunctorMap s₁ t₁ (curriedTensor X.Modules) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap a' b' (curriedTensor X.Modules) (.up ℤ) := by
  have hn := HomologicalComplex.mapBifunctorComparison_naturality
    (tensorResolutionRestrictionTensorNatIso j).hom (.up ℤ) a b
  dsimp only [tensorResolutionRestrictionTotalIso, asIso_hom]
  rw [reassoc_of% hn, tensorResolution_totalTensor_comp,
    tensorResolution_totalTensor_comp, ha, hb]

end AlgebraicGeometry
```

## New

The item's public imports:

```lean
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality
```

The companion module:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTensorNaturality

/-! # Tensor-resolution naturality

Re-export the source composition and restriction-square lemmas. Using their canonical
implementations allows this path and the comparison-naturality compatibility path to be
imported together without duplicate declarations.
-/
```

The upstream implementations of `tensorResolution_totalTensor_comp` and
`tensorResolution_restrictedTensor_square` have the same signatures as the replaced copies.
Their monoidal and zero-morphism local instances have the same constructions. The canonical
`tensorResolutionRestrictionTensorMap` remains the composite of
`tensorResolutionRestrictionTotalIso.hom` and `HomologicalComplex.mapBifunctorMap`.
No mathematical statement, definition, target meaning, or upstream file changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality --uses`
reports the two active downstream modules below (the two lemma names have no active uses
outside their defining module). The corresponding command for the item reports no active
importers. A source-only import graph including quarantine adds the nine archived consumers
below. All are unclaimed at this repair. None needs an adaptation. The two active consumer
sources compile unchanged against the delivered companion (26.8 s and 12.7 s), with existing
style and unused-simp warnings only; archives remain in quarantine. Both delivered modules
and the two-import regression compile without warnings. Neither consumer is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality | unclaimed | Replace duplicate implementation with canonical public re-export. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence | unclaimed | Direct importer; same declarations and instance constructions. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents | unclaimed | Direct importer; same restriction comparison and tensor API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartAugmentationNaturality | unclaimed, quarantined | Transitive importer; no statement changes. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality | unclaimed, quarantined | Same restricted tensor map. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartSummandNaturality | unclaimed, quarantined | Same restricted tensor map. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorNaturality | unclaimed, quarantined | Same restricted tensor map. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality | unclaimed, quarantined | Same restricted tensor map. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorTransport | unclaimed, quarantined | Transitive importer; no statement changes. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality | unclaimed, quarantined | Four applications of the same restriction-square lemma. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence | unclaimed, quarantined | Same restricted tensor map. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence | unclaimed, quarantined | Its two import paths now share canonical declarations. |

Neither delivered module has a DAG Lean attachment; the relevant dependent node
`new-h4-qcoh-tensor-comparison-restriction-naturality` retains its statement and proof route.
No node, quarantine source, or `WeilConjectures` declaration is removed or modified.

## Status

landed 20261022T043930-L-1099301 2026-10-22 (merge of deliver/E1/Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality)
