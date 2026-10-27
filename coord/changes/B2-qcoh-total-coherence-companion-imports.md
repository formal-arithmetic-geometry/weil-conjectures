# AlgebraicGeometry.tensorResolutionChartRestrictionComplexIso

## Reason

Complete the zero-hole rework's import compatibility repair. The current F1 landing
already re-exports the adopted TotalCoherence implementation. It cannot be combined
with the old explicit Sheaf RestrictionCoherence and TotalComponents dependencies:
those modules still redeclare constants supplied by the source module. A scratch
module importing all three reproduces this failure even after compiling the latest
TensorNaturality compatibility repair into the scratch overlay:

```text
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence failed,
environment already contains 'AlgebraicGeometry.TensorResolutionRestrictionCoherence_localInst1'
from Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence
```

The original companions compile individually (with their existing style warnings),
so this failure isolates the interaction between the import paths.

Replace the two unclaimed companion implementations with public imports of their
proved source equivalents. Retain the item's source import and restore its explicit
Sheaf companion import paths, now referring to the same constants. This is an actual
mixed-import repair, not a repeat of F1's already-landed single-module restoration.
No adopted-source file, archive, target, or mathematical definition is changed.

## Old

`Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence

/-! # Total tensor comparisons under successive affine restrictions

Compatibility import for `AlgebraicGeometry.tensorResolutionChartRestrictionComplexIso`,
`AlgebraicGeometry.tensorResolutionChartRestriction_total_inv`, and
`AlgebraicGeometry.tensorResolutionChartRestriction_total`.

The source module supplies the componentwise restriction isomorphism and the same two proved
coherence identities. Re-exporting it avoids mixing the Sheaf and source copies of their
common tensor-naturality dependencies.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence`:

```lean
module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartRestriction
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionRestrictionCoherence_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionRestrictionCoherence_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionRestrictionCoherence_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionRestrictionCoherence_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Restricting a module morphism uses its section map on the image open. -/
theorem tensorResolution_restrict_map_apply {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {F G : Y.Modules} (f : F ⟶ G)
    (W : X.Opens) (s : Γ(F.restrict j, W)) :
    ((restrictFunctor j).map f).app W s = f.app (j ''ᵁ W) s := rfl

/-- Pure tensor sections commute with any presheaf restriction map. -/
theorem tensorResolution_presheaf_map_tmul {X : Scheme.{u}} (F G : X.Modules)
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (s : Γ(F, U.unop)) (t : Γ(G, U.unop)) :
    (F ⊗ G).presheaf.map i (tmulSection s t) =
      tmulSection (F.presheaf.map i s) (G.presheaf.map i t) := by
  have ht := tmulSection_map (M := F) (N := G) (leOfHom i.unop) s t
  change (F ⊗ G).presheaf.map i (tmulSection s t) =
    tmulSection (F.presheaf.map i s) (G.presheaf.map i t) at ht
  exact ht

/-- The normalized tensor restriction comparisons respect successive affine restrictions. -/
theorem tensorResolutionChartRestriction_tensor_inv (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (F G : Y.Modules) :
    (((tensorResolutionChartRestrictionIso Y V U h).hom.app F) ⊗ₘ
        ((tensorResolutionChartRestrictionIso Y V U h).hom.app G)) ≫
        (tensorResolutionRestrictionTensor V.2.fromSpec F G).inv =
      (tensorResolutionRestrictionTensor (Spec.map (Y.presheaf.map (homOfLE h).op))
        (F.restrict U.2.fromSpec) (G.restrict U.2.fromSpec)).inv ≫
        (restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
          (tensorResolutionRestrictionTensor U.2.fromSpec F G).inv ≫
        (tensorResolutionChartRestrictionIso Y V U h).hom.app (F ⊗ G) := by
  apply tensorResolution_tensor_hom_ext
  intro W s t
  simp only [Hom.comp_app, ConcreteCategory.comp_apply,
    tensorHom_app_tmulSection, tensorResolutionRestrictionTensor_inv_tmul]
  simp only [tensorResolutionChartRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app]
  simp only [tensorResolution_restrict_map_apply, tensorResolutionRestrictionTensor_inv_tmul]
  erw [tensorResolutionRestrictionTensor_inv_tmul
    (Spec.map (Y.presheaf.map (homOfLE h).op))
    (F.restrict U.2.fromSpec) (G.restrict U.2.fromSpec) W s t]
  erw [tensorResolutionRestrictionTensor_inv_tmul U.2.fromSpec F G
    ((Spec.map (Y.presheaf.map (homOfLE h).op)) ''ᵁ W) s t]
  erw [tensorResolution_presheaf_map_tmul F G, tensorResolution_presheaf_map_tmul F G]
  rfl

end AlgebraicGeometry
```

`Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents`:

```lean
module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionTotalComponents_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionTotalComponents_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionTotalComponents_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionTotalComponents_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Total tensor maps on their coproduct summands. -/
@[reassoc] theorem tensorResolution_ι_totalTensorMap {X : Scheme.{u}}
    {E E' F F' : CochainComplex X.Modules ℤ} (a : E ⟶ E') (b : F ⟶ F')
    (p q i : ℤ) (h : p + q = i) :
    HomologicalComplex.ιMapBifunctor E F (curriedTensor X.Modules) (.up ℤ) p q i h ≫
        (HomologicalComplex.mapBifunctorMap a b (curriedTensor X.Modules) (.up ℤ)).f i =
      (a.f p ⊗ₘ b.f q) ≫
        HomologicalComplex.ιMapBifunctor E' F' (curriedTensor X.Modules) (.up ℤ) p q i h := by
  rw [tensorHom_def]
  exact HomologicalComplex.ι_mapBifunctorMap a b (curriedTensor X.Modules) (.up ℤ) p q i h

/-- Forward restriction comparison on one total tensor summand. -/
@[reassoc] theorem tensorResolution_map_ι_restrictionTotal_hom {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (E F : CochainComplex Y.Modules ℤ)
    (p q i : ℤ) (h : p + q = i) :
    (Scheme.Modules.restrictFunctor j).map
        (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i h) ≫
        (tensorResolutionRestrictionTotalIso j E F).hom.f i =
      (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F)
          (curriedTensor X.Modules) (.up ℤ) p q i h := by
  dsimp only [tensorResolutionRestrictionTotalIso, asIso_hom,
    HomologicalComplex.mapBifunctorComparison_f]
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (tensorResolutionRestrictionTensorNatIso j).hom (.up ℤ) E F p q i h

/-- Inverse restriction comparison on one total tensor summand. -/
@[reassoc] theorem tensorResolution_ι_restrictionTotal_inv {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (E F : CochainComplex Y.Modules ℤ)
    (p q i : ℤ) (h : p + q = i) :
    HomologicalComplex.ιMapBifunctor
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E)
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F)
        (curriedTensor X.Modules) (.up ℤ) p q i h ≫
        (tensorResolutionRestrictionTotalIso j E F).inv.f i =
      (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).inv ≫
        (Scheme.Modules.restrictFunctor j).map
          (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i h) := by
  apply (cancel_mono ((tensorResolutionRestrictionTotalIso j E F).hom.f i)).1
  have hi : (tensorResolutionRestrictionTotalIso j E F).inv.f i ≫
      (tensorResolutionRestrictionTotalIso j E F).hom.f i = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f ↦ f.f i) (tensorResolutionRestrictionTotalIso j E F).inv_hom_id
  rw [Category.assoc, hi, Category.comp_id]
  dsimp only [tensorResolutionRestrictionTotalIso, asIso_hom,
    HomologicalComplex.mapBifunctorComparison_f]
  rw [Category.assoc, HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  change _ = (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).inv ≫
    (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).hom ≫ _
  simp

end AlgebraicGeometry
```

## New

`Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents

/-! # Total tensor comparisons under successive affine restrictions

Compatibility import for `AlgebraicGeometry.tensorResolutionChartRestrictionComplexIso`,
`AlgebraicGeometry.tensorResolutionChartRestriction_total_inv`, and
`AlgebraicGeometry.tensorResolutionChartRestriction_total`.

The source module supplies the componentwise restriction isomorphism and the same two proved
coherence identities. Re-exporting it avoids mixing the Sheaf and source copies of their
common tensor-naturality dependencies. The explicit Sheaf dependency paths re-export the
same canonical declarations and remain compatible with this module.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence

/-! # Tensor restriction coherence

Re-export the canonical section formulas and successive affine tensor restriction identity.
This path can then be imported with the total-coherence compatibility module without
loading duplicate declarations.
-/

@[expose] public section
```

`Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalComponents

/-! # Components of total tensor comparisons

Re-export the canonical coproduct-summand formulas for total tensor maps and restriction
comparisons, including their reassociated forms. This keeps the component and total-coherence
compatibility paths in the same declaration environment.
-/

@[expose] public section
```

All six companion theorem statements compare identically with the source theorem
statements after the project's declaration parser normalizes whitespace. Their names,
visibility and reassoc attributes are preserved. The three TotalComponents reassociated
lemmas are also re-exported. Local monoidal and zero-map instances have the same names
and constructions in the canonical implementation. The existing concrete complex
restriction isomorphism and forward/inverse total coherence identities remain exactly
the source constants already exported by the current item.

## Users

The project's downstream tool reports zero live downstream modules for each companion.
A source search through lean/ and quarantine/ finds only the archived TotalCoherence
module importing them directly. It is replaced by the live item, which explicitly imports
both compatibility paths in this delivery. No current claim file exists for either
companion. No forced adaptation of a held module is involved.

The six archived direct importers of TotalCoherence are included below; their declarations
retain the same canonical types. No archive is edited or withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence | B2, this item | Publicly imports both compatible companion paths. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence | unclaimed | Re-exports the three proved canonical restriction lemmas. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents | unclaimed | Re-exports the three component lemmas and their reassoc forms. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartAugmentationNaturality | quarantined | Identical total restriction API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorTransport | quarantined | Identical total restriction API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence | quarantined | Identical API; checked by compiling its unchanged archive. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality | quarantined | Identical total restriction API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality | quarantined | Identical total restriction API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartSummandNaturality | quarantined | Identical total restriction API. |

No DAG node has its Lean attachment at any of the three modules. The parent node
new-t3-qcoh-tensor-resolution-chart-comparison-naturality still uses the same total
restriction theorem in step 3. Its proof, dependencies and unit route remain applicable;
no node edit or target-statement review is required.

## Status

landed 20261022T113829-L-281671 2026-10-22 (merge of deliver/B2/Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence)
