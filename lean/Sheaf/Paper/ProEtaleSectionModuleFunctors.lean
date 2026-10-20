/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SectionModuleOperationsData
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import Sheaf.Paper.InverseImageModuleFlat

import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Normalized tensors on the existing pro-etale module functors

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pd-proetale-section-module-functors).

## Main definitions

- `coefficientMap`: the structural section-ring map adjunct to the condensed coefficient map.
- `pushforward`, `pullback`, `adjunction`: the actual ringed module operations and adjunction.
- `ordinaryTensorComparison`, `totalComparison`: uniquely normalized tensor comparisons.
- `pushforwardComposition`, `pullbackComposition`: geometric pasting and its adjunction mate.
- `extension`, `openAdjunction`: the actual open extension and restriction adjunction.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing ringed adjunction supplies this compact left-adjoint instance.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
instance pullback_isLeftAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).IsLeftAdjoint := (adjunction Λ f).isLeftAdjoint

/-- The existing ringed adjunction supplies this compact right-adjoint instance.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
instance pushforward_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pushforward Λ f).IsRightAdjoint := (adjunction Λ f).isRightAdjoint

/-- Direct image is additive on the unchanged underlying sheaf maps.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: evaluate addition of maps on each base-changed site object. -/
@[instance] theorem pushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pushforward Λ f).Additive := by
  exact Functor.additive_of_preserves_binary_products (pushforward Λ f)

/-- The sectionwise pullback is additive.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: its adjunction identifies it with scalar extension after additive inverse image. -/
@[instance] theorem pullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).Additive := by
  exact (adjunction Λ f).left_adjoint_additive

/-- The additive pullback preserves zero maps without unfolding its composite construction.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) pullback_preservesZero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (pullback Λ f)

/-- The fixed additive equivalence preserves zero maps.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) equivalence_preservesZero (X : Scheme.{u}) :
    (equivalence Λ X).functor.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (equivalence Λ X).functor

/-- Pullback is exact for pulled-back condensed coefficients: alpha_f is invertible.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: transport the exact internal upperStar; its coefficient scalar change is an
isomorphism and inverse image is exact. -/
@[instance] theorem pullback_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pullback Λ f) := by
  exact ((InternalModuleOperations.internal_module_operations_transport Λ).2.2.2.1 f).1.mp
    (inferInstance : PreservesFiniteLimits (CondensedRing.upperStar Λ f))

/-- Pullback preserves finite colimits by its module adjunction.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: a left adjoint preserves colimits. -/
@[instance] theorem pullback_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback Λ f) := by
  have := (adjunction Λ f).leftAdjoint_preservesColimits
  infer_instance

/-- The existing exact-equivalence theorem supplies this compact finite-limit instance.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors). -/
instance equivalence_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (equivalence Λ X).functor :=
  ((InternalModuleOperations.internal_module_operations_transport Λ).1 X).2.2.1

/-- The existing exact-equivalence theorem supplies this compact finite-colimit instance.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors). -/
instance equivalence_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (equivalence Λ X).functor :=
  ((InternalModuleOperations.internal_module_operations_transport Λ).1 X).2.2.2.1

/-- The sectionwise equivalence preserves homology.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors).
Proof: unchanged underlying sheaves identify kernels, images and cokernels. -/
@[instance] theorem equivalence_preservesHomology (X : Scheme.{u}) :
    (equivalence Λ X).functor.PreservesHomology := by
  infer_instance

/-- The internal relative tensor preserves zero maps in its first variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) internalTensor_preservesZero (X : Scheme.{u}) :
    (curriedTensor (internalModules Λ X)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (curriedTensor (internalModules Λ X))

/-- The internal relative tensor preserves zero maps in its second variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) internalTensorObj_preservesZero (X : Scheme.{u})
    (M : internalModules Λ X) :
    ((curriedTensor (internalModules Λ X)).obj M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive ((curriedTensor (internalModules Λ X)).obj M)

/-- The sectionwise relative tensor preserves zero maps in its first variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) sectionTensor_preservesZero (X : Scheme.{u}) :
    (curriedTensor (modules Λ X)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (curriedTensor (modules Λ X))

/-- The sectionwise relative tensor preserves zero maps in its second variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) sectionTensorObj_preservesZero (X : Scheme.{u})
    (M : modules Λ X) :
    ((curriedTensor (modules Λ X)).obj M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive ((curriedTensor (modules Λ X)).obj M)

/-- The actual sectionwise pairing on internal direct image specifies its lax structure.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors). -/
def InternalPushNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (CondensedRing.lowerStar Λ f).LaxMonoidal) : Prop :=
  ∀ (M N : internalModules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((CondensedRing.lowerStar Λ f).obj M).X.obj.obj U)
    (y : ((CondensedRing.lowerStar Λ f).obj N).X.obj.obj U),
    ((m.μ M N).hom.hom.app U)
        (internalPureTensor Λ Y _ _ U x y) =
      internalPureTensor Λ X M N
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U) x y

private theorem laxMonoidal_ext_mu {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (m n : F.LaxMonoidal) (h : ∀ X Y, m.μ X Y = n.μ X Y) : m = n := by
  let Rm : MonObj (F.obj (𝟙_ C)) := by
    letI := m
    exact F.monObjObj (𝟙_ C)
  let Rn : MonObj (F.obj (𝟙_ C)) := by
    letI := n
    exact F.monObjObj (𝟙_ C)
  have hmul : Rm.mul = Rn.mul :=
    congrArg (fun k ↦ k ≫ F.map (λ_ (𝟙_ C)).hom) (h (𝟙_ C) (𝟙_ C))
  have hε := congrArg (fun p : MonObj (F.obj (𝟙_ C)) ↦ p.one) (MonObj.ext Rm Rn hmul)
  change m.ε ≫ F.map (𝟙 (𝟙_ C)) = n.ε ≫ F.map (𝟙 (𝟙_ C)) at hε
  apply Functor.LaxMonoidal.ext
  · exact (cancel_mono (F.map (𝟙 (𝟙_ C)))).mp hε
  · exact funext fun X ↦ funext fun Y ↦ h X Y

private theorem internalPureTensor_hom_ext (X : Scheme.{u})
    (M N H : internalModules Λ X) {f g : M ⊗ N ⟶ H}
    (h : ∀ (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      (f.hom.hom.app U) (internalPureTensor Λ X M N U x y) =
        (g.hom.hom.app U) (internalPureTensor Λ X M N U x y)) : f = g := by
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorObjπ M N)).mp
  apply Sheaf.tensor_hom_ext
  ext U t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x y => exact h U x y

private theorem internalPushNormalized_unique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m n : (CondensedRing.lowerStar Λ f).LaxMonoidal)
    (hm : InternalPushNormalized Λ f m) (hn : InternalPushNormalized Λ f n) : m = n := by
  apply laxMonoidal_ext_mu
  intro M N
  apply internalPureTensor_hom_ext Λ Y
  intro U x y
  exact (hm M N U x y).trans (hn M N U x y).symm

@[instance_reducible]
private noncomputable def canonicalInternalPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).LaxMonoidal := by
  letI : (CondensedRing.upperStar Λ f).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal

private theorem mapMod_tensorπ_delta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    (ProEtale.upperStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) ≫
        ((ProEtale.upperStar Ab.{u + 1} f).mapModTensorIso M N).inv.hom =
      Functor.OplaxMonoidal.δ (ProEtale.upperStar Ab.{u + 1} f) M.X N.X ≫
        Mod.tensorObjπ
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M)
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj N) := by
  let F := ProEtale.upperStar Ab.{u + 1} f
  apply (cancel_mono (F.mapModTensorIso M N).hom.hom).mp
  rw [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id]
  change F.map (Mod.tensorObjπ M N) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rw [Category.assoc, F.tensorπ_mapModTensorIso_hom_hom M N, ← Category.assoc,
    Functor.Monoidal.δ_μ, Category.id_comp]

set_option maxHeartbeats 600000 in
-- The scalar-extension and tensor comparison instances involve large coefficient types.
private theorem upperStar_tensorπ_delta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    let A := ProEtale.upperStar Ab.{u + 1} f
    let T := A.mapMod (condensedRingObj Λ Y)
    let E := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)
    A.map (Mod.tensorObjπ M N) ≫
        Mod.extendUnitHom (condensedPullbackHom Λ f) (T.obj (M ⊗ N)) ≫
        ((CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N).hom =
      Functor.OplaxMonoidal.δ A M.X N.X ≫
        Mod.tensorObjπ
          ((Mod.comap (asIso (condensedPullbackHom Λ f)).inv).obj (T.obj M))
          ((Mod.comap (asIso (condensedPullbackHom Λ f)).inv).obj (T.obj N)) ≫
        ((E.inv.app (T.obj M) ⊗ₘ E.inv.app (T.obj N))).hom := by
  dsimp only
  let A := ProEtale.upperStar Ab.{u + 1} f
  let T := A.mapMod (condensedRingObj Λ Y)
  let φ := condensedPullbackHom Λ f
  let E := Mod.extendScalarsIsoComapInv φ
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendRestrictAdjunction φ).unit.naturality
      (Functor.OplaxMonoidal.δ T M N))
  simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
    ] at hn
  change A.map (Mod.tensorObjπ M N) ≫ Mod.extendUnitHom φ (T.obj (M ⊗ N)) ≫
    (((Mod.extendScalars φ).map (Functor.OplaxMonoidal.δ T M N)) ≫
      Functor.OplaxMonoidal.δ (Mod.extendScalars φ) (T.obj M) (T.obj N)).hom = _
  rw [Mod.comp_hom', ← Category.assoc, ← Category.assoc]
  change (Functor.OplaxMonoidal.δ T M N).hom ≫
    Mod.extendUnitHom φ (T.obj M ⊗ T.obj N) =
    Mod.extendUnitHom φ (T.obj (M ⊗ N)) ≫
    ((Mod.extendScalars φ).map (Functor.OplaxMonoidal.δ T M N)).hom at hn
  rw [Category.assoc (A.map (Mod.tensorObjπ M N)), ← hn]
  rw [Functor.Monoidal.transport_δ, Mod.comp_hom', Mod.comp_hom']
  simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (CondensedRing.extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f)]
  have hδ : (Functor.OplaxMonoidal.δ T M N).hom =
      (A.mapModTensorIso M N).inv.hom := rfl
  rw [← Category.assoc, ← Category.assoc, hδ, mapMod_tensorπ_delta Λ f M N]
  have hc : Mod.tensorObjπ (T.obj M) (T.obj N) ≫
      (Mod.comapTensorIso (asIso φ).inv (T.obj M) (T.obj N)).inv.hom =
      Mod.tensorObjπ ((Mod.comap (asIso φ).inv).obj (T.obj M))
        ((Mod.comap (asIso φ).inv).obj (T.obj N)) := by
    apply (cancel_mono (Mod.comapTensorIso (asIso φ).inv (T.obj M) (T.obj N)).hom.hom).mp
    rw [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id]
    change Mod.tensorObjπ (T.obj M) (T.obj N) ≫ 𝟙 _ = _
    rw [Category.comp_id, Mod.tensorπ_comapTensorIso_hom_hom]
  change ((Functor.OplaxMonoidal.δ A M.X N.X ≫ Mod.tensorObjπ (T.obj M) (T.obj N)) ≫
    (Mod.comapTensorIso (asIso φ).inv (T.obj M) (T.obj N)).inv.hom) ≫ _ = _
  simpa only [Category.assoc] using congrArg
    (fun k ↦ Functor.OplaxMonoidal.δ A M.X N.X ≫ k ≫
      ((E.inv.app (T.obj M) ⊗ₘ E.inv.app (T.obj N))).hom) hc


private theorem counit_underlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internalModules Λ X) :
    Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj
          ((CondensedRing.lowerStar Λ f).obj M)) ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counit.app M.X := by
  let adj := CondensedRing.upperStarLowerStarAdjunction Λ f
  let a := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  apply (a.homEquiv _ _).injective
  have hi : adj.homEquiv _ _ (adj.counit.app M) = 𝟙 _ := by
    have h := (adj.homEquiv _ M).apply_symm_apply (𝟙 _)
    rw [adj.homEquiv_symm_id] at h
    exact h
  have h := CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom Λ f
    ((CondensedRing.lowerStar Λ f).obj M) M (adj.counit.app M)
  change (adj.homEquiv _ _ (adj.counit.app M)).hom = _ at h
  rw [hi] at h
  have ha := (a.homEquiv _ M.X).apply_symm_apply (𝟙 _)
  rw [a.homEquiv_symm_id] at ha
  rw [Adjunction.homEquiv_unit]
  exact h.symm.trans ha.symm

private theorem normalized_of_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hc : ∀ M N : internalModules Λ X,
      Mod.tensorObjπ ((CondensedRing.lowerStar Λ f).obj M)
          ((CondensedRing.lowerStar Λ f).obj N) ≫
        ((canonicalInternalPush Λ f).μ M N).hom =
      Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N)) :
    InternalPushNormalized Λ f (canonicalInternalPush Λ f) := by
  intro M N U x y
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have h := NatTrans.IsMonoidal.tensor
    (τ := (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom) M.X N.X
  simp only [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    id_tensorHom_id, Category.id_comp, Category.comp_id, Functor.LaxMonoidal.comp_μ] at h
  have hp := congrArg (fun k ↦ (k.hom.app U)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((CondensedRing.lowerStar Λ f).obj M).X
      ((CondensedRing.lowerStar Λ f).obj N).X).app U) (x ⊗ₜ[ℤ] y))) (hc M N)
  have hU := congrArg (fun k ↦ (k.app U) (x ⊗ₜ[ℤ] y)) h
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      M.X N.X).app (F.op.obj U)) (x ⊗ₜ[ℤ] y) =
    ((Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X).hom.app U)
      (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        ((CondensedRing.lowerStar Λ f).obj M).X
        ((CondensedRing.lowerStar Λ f).obj N).X).app U) (x ⊗ₜ[ℤ] y)) at hU
  exact hp.trans (congrArg (fun z ↦
    (((ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N)).hom.app U) z) hU.symm)

private theorem tensorπ_natural {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] [HasCoequalizers C]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    {R : C} [MonObj R] [IsCommMonObj R] {M N P Q : Mod C R}
    (g : M ⟶ P) (h : N ⟶ Q) :
    Mod.tensorObjπ M N ≫ (g ⊗ₘ h).hom =
      (g.hom ⊗ₘ h.hom) ≫ Mod.tensorObjπ P Q := by
  rw [MonoidalCategory.tensorHom_def, Mod.comp_hom',
    Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft, ← Category.assoc,
    ← MonoidalCategory.tensorHom_def]

set_option maxHeartbeats 600000 in
-- The comparison expands scalar extension only in this underlying-sheaf calculation.
private theorem canonical_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ X) :
    Mod.tensorObjπ ((CondensedRing.lowerStar Λ f).obj M)
        ((CondensedRing.lowerStar Λ f).obj N) ≫
      ((canonicalInternalPush Λ f).μ M N).hom =
    Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) := by
  let : (CondensedRing.upperStar Λ f).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal
  let A := ProEtale.upperStar Ab.{u + 1} f
  let G := ProEtale.lowerStar Ab.{u + 1} f
  let H := CondensedRing.lowerStar Λ f
  let T := A.mapMod (condensedRingObj Λ Y)
  let φ := condensedPullbackHom Λ f
  let E := Mod.extendScalarsIsoComapInv φ
  let adj := CondensedRing.upperStarLowerStarAdjunction Λ f
  let a := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  let cM := adj.counit.app M
  let cN := adj.counit.app N
  have hu (K : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (A.obj (condensedRingObj Λ Y))) :
      (E.inv.app K).hom = Mod.extendUnitHom φ K := by
    apply (cancel_mono (E.hom.app K).hom).mp
    rw [← Mod.comp_hom', E.inv_hom_id_app]
    exact (CondensedRing.extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f K).symm
  have hM : (E.inv.app (T.obj (H.obj M)) ≫ cM).hom = a.counit.app M.X := by
    rw [Mod.comp_hom', hu]
    exact counit_underlying Λ f M
  have hN : (E.inv.app (T.obj (H.obj N)) ≫ cN).hom = a.counit.app N.X := by
    rw [Mod.comp_hom', hu]
    exact counit_underlying Λ f N
  have h := congrArg (fun k ↦ k ≫ (cM ⊗ₘ cN).hom)
    (upperStar_tensorπ_delta Λ f (H.obj M) (H.obj N))
  simp only [Category.assoc] at h
  have ht : ((E.inv.app (T.obj (H.obj M)) ⊗ₘ E.inv.app (T.obj (H.obj N)))).hom ≫
      (cM ⊗ₘ cN).hom =
      ((E.inv.app (T.obj (H.obj M)) ≫ cM) ⊗ₘ
        (E.inv.app (T.obj (H.obj N)) ≫ cN)).hom := by
    rw [← Mod.comp_hom', tensorHom_comp_tensorHom]
  rw [ht] at h
  have hn := tensorπ_natural (E.inv.app (T.obj (H.obj M)) ≫ cM)
    (E.inv.app (T.obj (H.obj N)) ≫ cN)
  rw [hM, hN] at hn
  have hr := congrArg (fun k ↦ Functor.OplaxMonoidal.δ A (H.obj M).X (H.obj N).X ≫ k) hn
  have hh := h.trans hr
  have hμ : a.homEquiv _ _ (Functor.OplaxMonoidal.δ A (G.obj M.X) (G.obj N.X) ≫
      (a.counit.app M.X ⊗ₘ a.counit.app N.X)) =
      Functor.LaxMonoidal.μ G M.X N.X := by
    apply (a.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (a.map_μ_comp_counit_app_tensor M.X N.X).symm
  let g := Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f)
    (H.obj M) (H.obj N) ≫ (cM ⊗ₘ cN)
  have hm := CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom Λ f
    (H.obj M ⊗ H.obj N) (M ⊗ N) g
  change (adj.homEquiv _ _ g).hom = a.homEquiv _ _
    (Mod.extendUnitHom φ (T.obj (H.obj M ⊗ H.obj N)) ≫ g.hom) at hm
  change Mod.tensorObjπ (H.obj M) (H.obj N) ≫ (adj.homEquiv _ _ g).hom = _
  rw [hm]
  calc
    _ = a.homEquiv _ _ (A.map (Mod.tensorObjπ (H.obj M) (H.obj N)) ≫
        Mod.extendUnitHom φ (T.obj (H.obj M ⊗ H.obj N)) ≫ g.hom) := by
      rw [Adjunction.homEquiv_naturality_left]
    _ = a.homEquiv _ _ (Functor.OplaxMonoidal.δ A (H.obj M).X (H.obj N).X ≫
        (a.counit.app M.X ⊗ₘ a.counit.app N.X) ≫ Mod.tensorObjπ M N) := by
      apply congrArg
      convert hh using 1 <;> rfl
    _ = a.homEquiv _ _ (Functor.OplaxMonoidal.δ A (G.obj M.X) (G.obj N.X) ≫
        (a.counit.app M.X ⊗ₘ a.counit.app N.X)) ≫ G.map (Mod.tensorObjπ M N) := by
      rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
      rfl
    _ = _ := congrArg (fun k ↦ k ≫ G.map (Mod.tensorObjπ M N)) hμ

private theorem canonicalInternalPush_normalized {X Y : Scheme.{u}} (f : X ⟶ Y) :
    InternalPushNormalized Λ f (canonicalInternalPush Λ f) :=
  normalized_of_projection Λ f (canonical_projection Λ f)

/-- Direct image has the uniquely specified local-pure-tensor lax structure.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors).
Proof: its sectionwise bilinear pairing is balanced through the adjunct coefficient
map and restriction-compatible. Sheafify and use the relative-tensor coequalizer.
The associativity and unit equations hold on pure tensors. Local generation gives
uniqueness of the tensor maps; the regular-module unit and the unitor law then give
uniqueness of the unit map as well. -/
theorem internalPushNormalized_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! m : (CondensedRing.lowerStar Λ f).LaxMonoidal, InternalPushNormalized Λ f m := by
  refine ⟨canonicalInternalPush Λ f, canonicalInternalPush_normalized Λ f, ?_⟩
  intro m hm
  exact internalPushNormalized_unique Λ f m _ hm (canonicalInternalPush_normalized Λ f)

/-- Choose the uniquely characterized direct-image pairing, not an arbitrary map.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance internalPushLax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).LaxMonoidal :=
  (internalPushNormalized_existsUnique Λ f).exists.choose

/-- The actual oplax module pullback is the mate of the specified direct-image pairing.
Source: Stacks 03D7 and 03EL
(blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance internalPullOplax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).OplaxMonoidal :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).leftAdjointOplaxMonoidal

private theorem canonicalInternalPull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := canonicalInternalPush Λ f
    (CondensedRing.upperStarLowerStarAdjunction Λ f).leftAdjointOplaxMonoidal =
      (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal := by
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).laxMonoidalEquivOplaxMonoidal
    |>.apply_symm_apply (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal

private theorem internalPushLax_eq_canonical {X Y : Scheme.{u}} (f : X ⟶ Y)
    :
    internalPushLax Λ f = canonicalInternalPush Λ f := by
  apply internalPushNormalized_unique Λ f
  · exact (internalPushNormalized_existsUnique Λ f).exists.choose_spec
  · exact canonicalInternalPush_normalized Λ f
private theorem internalPullOplax_eq_canonical {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullOplax Λ f = (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal := by
  change (CondensedRing.upperStarLowerStarAdjunction Λ f).laxMonoidalEquivOplaxMonoidal
    (internalPushLax Λ f) = _
  rw [internalPushLax_eq_canonical Λ f]
  exact canonicalInternalPull_eq Λ f

/-- The pullback mate tensor component is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: on extension-of-scalars pure tensors the map sends s tensor (m tensor n)
to (s tensor m) tensor (1 tensor n). Its inverse multiplies the two scalar factors.
Both respect balancing and commute with restriction, so sheafify to inverse maps. -/
@[instance] theorem internalPull_delta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    IsIso (Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f) M N) := by
  rw [internalPullOplax_eq_canonical Λ f]
  let := CondensedRing.monoidal_upperStar Λ f
  infer_instance

/-- The unit component of the pullback mate is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: scalar extension sends the regular module to the regular module; multiplication
and insertion of 1 are mutually inverse by the unit and balancing relations. -/
@[instance] theorem internalPull_eta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Functor.OplaxMonoidal.η (CondensedRing.upperStar Λ f)) := by
  rw [internalPullOplax_eq_canonical Λ f]
  let := CondensedRing.monoidal_upperStar Λ f
  infer_instance

/-- Strong module pullback, retaining the mate oplax maps just constructed.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance internalPullMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (CondensedRing.upperStar Λ f)

/-- Pullback preserves flat internal modules.
Source: Stacks 03EL and 0G7E
(blueprint: def-pd-proetale-section-module-functors).
Proof: tensor with a pulled-back flat module is the pullback of tensor before scalar
extension. Exact inverse image and flatness make its acyclic short-exact test exact. -/
@[instance] theorem internalPull_preservesFlat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).PreservesFlat := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let R := condensedRingObj Λ Y
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  have h := ProEtale.inverseImageModule_preservesFlat f R (condensedRingObj Λ X) ρ
  let e : CondensedRing.upperStar Λ f ≅ Mod.mapModComap ρ :=
    Functor.isoWhiskerLeft (G.mapMod R)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  exact ⟨fun hM ↦ ObjectProperty.flat.prop_of_iso (e.symm.app _) (h.flat_obj hM)⟩

/-- The sectionwise pure-tensor normalization of ringed direct image.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors). -/
def PushNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (pushforward Λ f).LaxMonoidal) : Prop :=
  ∀ (M N : modules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((pushforward Λ f).obj M).val.obj U)
    (y : ((pushforward Λ f).obj N).val.obj U),
    ((m.μ M N).val.app U)
        (sectionPureTensor Λ Y _ _ U x y) =
      sectionPureTensor Λ X M N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U) x y

/-- The ringed direct-image pairing is uniquely specified, including its unit.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors).
Proof: the sectionwise balanced pairing sheafifies. Coherence is checked on pure
tensors. The tensor universal property gives uniqueness of the tensorator, and its
regular-module unit equation forces the coefficient-map unit. -/
theorem pushNormalized_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! m : (pushforward Λ f).LaxMonoidal, PushNormalized Λ f m := by
  sorry

/-- The specified ringed direct-image pairing.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance pushLax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pushforward Λ f).LaxMonoidal :=
  (pushNormalized_existsUnique Λ f).exists.choose

/-- The specified ordinary ringed pullback comparison, as the mate of direct image.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance pullOplax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).OplaxMonoidal := (adjunction Λ f).leftAdjointOplaxMonoidal

/-- The ordinary ringed pullback comparison is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: its pure-tensor formula is s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n); the inverse multiplies the scalar factors.
The balancing relations give well-defined mutually inverse maps before sheafification. -/
@[instance] theorem pull_delta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ Y) :
    IsIso (Functor.OplaxMonoidal.δ (pullback Λ f) M N) := by
  sorry

/-- The ordinary ringed pullback comparison on the unit is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: extension of scalars of a regular module is the regular module. -/
@[instance] theorem pull_eta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Functor.OplaxMonoidal.η (pullback Λ f)) := by
  sorry

/-- The strong ringed pullback retains the specified oplax mate maps.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance pullMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback Λ f)

private theorem sectionPureTensor_hom_ext (X : Scheme.{u}) (M N H : modules Λ X)
    {f g : M ⊗ N ⟶ H}
    (h : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      (f.val.app U) (sectionPureTensor Λ X M N U x y) =
        (g.val.app U) (sectionPureTensor Λ X M N U x y)) : f = g := by
  let R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R.obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

/-- The existing pure-tensor comparison is uniquely specified by its local formula.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors).
Proof: use internal_section_tensor_comparison for existence. Local pure tensors
generate the relative tensor after sheafification; their displayed images
therefore determine the sheaf-module map and hence the isomorphism uniquely. -/
theorem ordinaryTensorComparison_existsUnique (X : Scheme.{u})
    (M N : internalModules Λ X) :
    ∃! t : (equivalence Λ X).functor.obj (M ⊗ N) ≅
        (equivalence Λ X).functor.obj M ⊗ (equivalence Λ X).functor.obj N,
      ∀ (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
        (t.hom.val.app U)
            (internalPureTensor Λ X M N U x y) =
          sectionPureTensor Λ X
            ((equivalence Λ X).functor.obj M) ((equivalence Λ X).functor.obj N) U x y := by
  obtain ⟨e, e₀, he, _⟩ :=
    (InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).2
  refine ⟨e M N, he M N, ?_⟩
  intro t ht
  apply Iso.ext
  apply (cancel_epi (e M N).inv).mp
  apply sectionPureTensor_hom_ext Λ X
  intro U x y
  change M.X.obj.obj U at x
  change N.X.obj.obj U at y
  have hxy : ((e M N).inv.val.app U)
      (sectionPureTensor Λ X
        ((equivalence Λ X).functor.obj M) ((equivalence Λ X).functor.obj N) U x y) =
      internalPureTensor Λ X M N U x y := by
    have hp := congrArg (fun z ↦ ((e M N).inv.val.app U) z) (he M N U x y)
    have hi := congrArg (fun k ↦ (k.val.app U) (internalPureTensor Λ X M N U x y))
      (e M N).hom_inv_id
    exact hp.symm.trans hi
  change (t.hom.val.app U) (((e M N).inv.val.app U) _) =
    ((e M N).hom.val.app U) (((e M N).inv.val.app U) _)
  exact (congrArg (t.hom.val.app U) hxy).trans
    ((ht U x y).trans ((he M N U x y).symm.trans
      (congrArg ((e M N).hom.val.app U) hxy).symm))

/-- The existing ordinary tensor comparison, selected by its unique pure-tensor formula.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
def ordinaryTensorComparison (X : Scheme.{u}) (M N : internalModules Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      (equivalence Λ X).functor.obj M ⊗ (equivalence Λ X).functor.obj N :=
  (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose

private theorem map_jointly_epi {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] {A : C} {I : Type*}
    (S : I → C) (ι : ∀ i, S i ⟶ A)
    (hι : ∀ {Z : C} (f g : A ⟶ Z), (∀ i, ι i ≫ f = ι i ≫ g) → f = g)
    {B : D} {f g : F.obj A ⟶ B}
    (h : ∀ i, F.map (ι i) ≫ f = F.map (ι i) ≫ g) : f = g := by
  let e := F.objObjPreimageIso B
  apply (cancel_mono e.inv).mp
  let f' := F.preimage (f ≫ e.inv)
  let g' := F.preimage (g ≫ e.inv)
  have hfg : f' = g' := by
    apply hι
    intro i
    apply F.map_injective
    simpa only [Functor.map_comp, f', g', Functor.map_preimage, ← Category.assoc]
      using congrArg (fun k ↦ k ≫ e.inv) (h i)
  simpa only [f', g', Functor.map_preimage] using congrArg F.map hfg

set_option maxHeartbeats 600000 in
-- The cochain total and section equivalence carry large tensor and universe instances.
/-- The total-complex comparison is uniquely determined on each direct-sum summand.
Source: Stacks 06YN (blueprint: def-pd-proetale-section-module-functors).
Proof: sum the normalized ordinary comparisons in each degree. Naturality commutes
with the two differential components, with the same sign (-1)^p. The coproduct
universal property gives uniqueness; the summed inverses give an inverse chain map. -/
theorem totalComparison_existsUnique (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    ∃! t : ((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor _)) ≅
      CochainComplex.mapBifunctor
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
        (curriedTensor _),
    ∀ (p q n : ℤ) (h : p + q = n),
      (equivalence Λ X).functor.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫ t.hom.f n =
        (ordinaryTensorComparison Λ X (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
            (curriedTensor _) p q n h := by
  obtain ⟨e, e₀, data⟩ :=
    (InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).2
  have he := data.1
  have htot := data.2.2.2.2.2.2.2.1
  have heq (M N : internalModules Λ X) : e M N = ordinaryTensorComparison Λ X M N :=
    (ordinaryTensorComparison_existsUnique Λ X M N).unique
      (he M N) (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec
  have hPQ := htot P Q
  obtain ⟨t, ht⟩ := hPQ
  refine ⟨t, ?_, ?_⟩
  · intro p q n h
    exact (ht p q n h).trans
      (congrArg (fun k ↦ k.hom ≫ _) (heq (P.X p) (Q.X q)))
  · intro s hs
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro n
    apply map_jointly_epi (equivalence Λ X).functor
      (fun i : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦ P.X i.val.1 ⊗ Q.X i.val.2)
      (fun i ↦ CochainComplex.ιMapBifunctor P Q (curriedTensor _)
        i.val.1 i.val.2 n i.property)
    · intro Z a b hab
      exact HomologicalComplex.mapBifunctor.hom_ext fun p q h ↦ hab ⟨(p, q), h⟩
    · rintro ⟨⟨p, q⟩, h⟩
      have heq' := congrArg (fun k ↦ k.hom ≫
        CochainComplex.ιMapBifunctor
          (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
          (curriedTensor _) p q n h) (heq (P.X p) (Q.X q))
      exact (hs p q n h).trans (heq'.symm.trans (ht p q n h).symm)

/-- The uniquely specified direct-sum total-complex comparison.
Source: Stacks 06YN (blueprint: def-pd-proetale-section-module-functors). -/
def totalComparison (X : Scheme.{u}) (P Q : CochainComplex (internalModules Λ X) ℤ) :=
  (totalComparison_existsUnique Λ X P Q).exists.choose

/-- Extension by zero is additive, since all its three specified factors are additive.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: its underlying maps are extension-by-zero maps of abelian sheaves; addition
is computed on each summand before sheafification. -/
@[instance] theorem extension_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extension Λ j).Additive := by
  exact (openAdjunction Λ j).left_adjoint_additive

/-- Extension by zero preserves finite limits.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: exactness of the internal open extension transfers through the two exact
equivalences, or can be checked on the unchanged underlying abelian sheaves. -/
@[instance] theorem extension_preservesFiniteLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (extension Λ j) := by
  exact ((InternalModuleOperations.internal_module_operations_transport Λ).2.2.2.2.1 j).1.mp
    (inferInstance : PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j))

/-- Extension by zero preserves finite colimits.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: it is the left adjoint in the specified open adjunction. -/
@[instance] theorem extension_preservesFiniteColimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (extension Λ j) := by
  have := (openAdjunction Λ j).leftAdjoint_preservesColimits
  infer_instance

/-- The regular-unit comparison is uniquely specified by fixing every scalar section.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors).
Proof: the unit clause of internal_section_tensor_comparison supplies the map.
The scalar identities determine every component, hence the natural isomorphism. -/
theorem ordinaryUnitComparison_existsUnique (X : Scheme.{u}) :
    ∃! t : (equivalence Λ X).functor.obj (𝟙_ (internalModules Λ X)) ≅ 𝟙_ (modules Λ X),
      ∀ (U : X.ProEtᵒᵖ) (r : (condensedRingObj Λ X).obj.obj U), (t.hom.val.app U) r = r := by
  obtain ⟨e, e₀, _, he₀, _⟩ :=
    (InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).2
  refine ⟨e₀, he₀, ?_⟩
  intro t ht
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact LinearMap.ext (fun r ↦ (ht U r).trans (he₀ U r).symm)

/-- The normalized tensor unit comparison fixes every section of the regular module.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
def ordinaryUnitComparison (X : Scheme.{u}) :
    (equivalence Λ X).functor.obj (𝟙_ (internalModules Λ X)) ≅ 𝟙_ (modules Λ X) :=
  (ordinaryUnitComparison_existsUnique Λ X).exists.choose

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
