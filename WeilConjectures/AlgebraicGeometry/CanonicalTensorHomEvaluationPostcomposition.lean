/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation

/-! # One-variable localized evaluation compatibility

## References

* Stacks Project, Tags 08DJ, 0A90 and 0A96
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private def evaluation (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := schemeDerivedTensorMonoidal X
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ⊗
      DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj M :=
  letI := schemeDerivedTensorMonoidal X
  ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
      𝟙 (DerivedCategory.Q.obj L)) ≫
    pullbackTensorModelMap X _ L ≫
    DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
    schemeHomResolutionInverse X M

private theorem tensor_naturality {C : Type*} [Category* C] [MonoidalCategory C]
    {A A' B B' L M M' : C} (a : A ⟶ A') (j : A' ⟶ B') (i : A ⟶ B)
    (b : B ⟶ B') (ε' : B' ⊗ L ⟶ M') (ε : B ⊗ L ⟶ M) (f : M ⟶ M')
    (h : a ≫ j = i ≫ b) (k : (b ⊗ₘ 𝟙 L) ≫ ε' = ε ≫ f) :
    (a ⊗ₘ 𝟙 L) ≫ (j ⊗ₘ 𝟙 L) ≫ ε' = ((i ⊗ₘ 𝟙 L) ≫ ε) ≫ f := by
  simp only [tensorHom_id] at k ⊢
  rw [← Category.assoc, ← comp_whiskerRight, h, comp_whiskerRight, Category.assoc, k]
  exact (Category.assoc _ _ _).symm

set_option maxHeartbeats 800000 in
-- Elaborating the fixed sheaf tensor and localization instances needs extra heartbeats.
set_option backward.isDefEq.respectTransparency.types true in
private theorem evaluation_chain_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (f : M ⟶ N) :
    letI := schemeDerivedTensorMonoidal X
    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        (𝟙 (op (DerivedCategory.Q.obj L)), DerivedCategory.Q.map f) ⊗ₘ
      𝟙 (DerivedCategory.Q.obj L)) ≫ evaluation X L N =
      evaluation X L M ≫ DerivedCategory.Q.map f := by
  let := schemeDerivedTensorMonoidal X
  let H := Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))
  let h := H.map (X := (op L, (schemeHomKInjectiveResolution X).obj M))
    (Y := (op L, (schemeHomKInjectiveResolution X).obj N))
    ((𝟙 L).op, (schemeHomKInjectiveResolution X).map f)
  have hi := schemeTensorHomUncurry_localized_evaluation X _ _ L L N N
    h (𝟙 L) (𝟙 N) (𝟙 _)
  have hf := schemeTensorHomUncurry_localized_evaluation X _ _ L L M N
    (𝟙 _) (𝟙 L) f (𝟙 _)
  have hid : ((𝟙 L).op, (schemeHomKInjectiveResolution X).map (𝟙 N)) =
      𝟙 (op L, (schemeHomKInjectiveResolution X).obj N) := by
    rw [(schemeHomKInjectiveResolution X).map_id, op_id]
    rfl
  rw [hid, H.map_id] at hi
  simp only [Category.comp_id, Category.id_comp, DerivedCategory.Q.map_id] at hi hf
  simp only [id_tensorHom_id, Category.id_comp] at hf
  have he : (DerivedCategory.Q.map h ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫
      (pullbackTensorModelMap X _ L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X _ L N (𝟙 _)) ≫
        schemeHomResolutionInverse X N) =
      (pullbackTensorModelMap X _ L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
        schemeHomResolutionInverse X M) ≫ DerivedCategory.Q.map f := hi.symm.trans hf
  have hn : (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
      (𝟙 (op (DerivedCategory.Q.obj L)), DerivedCategory.Q.map f) ≫
        (schemeDerivedInternalHomResolutionIso X L N).hom =
      (schemeDerivedInternalHomResolutionIso X L M).hom ≫ DerivedCategory.Q.map h := by
    have := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
    let I := CochainComplex.kInjectiveResolutionFunctor.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let e := Localization.fac ((𝟭 _).prod I ⋙ H ⋙ DerivedCategory.Q)
      (derivedInternalHom_inverts (Opens.grothendieckTopology X) X.sheaf I
        (CochainComplex.toKInjectiveResolution.{u} _)
        (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
      (DerivedCategory.Q.op.prod DerivedCategory.Q)
    have hn₀ := e.hom.naturality (X := (op L, M)) (Y := (op L, N))
      (𝟙 (op L), f)
    have hQ : (DerivedCategory.Q.op.prod DerivedCategory.Q).map
        (X := (op L, M)) (Y := (op L, N)) (𝟙 (op L), f) =
        (𝟙 (op (DerivedCategory.Q.obj L)), DerivedCategory.Q.map f) := by
      change ((DerivedCategory.Q.map (𝟙 L)).op, DerivedCategory.Q.map f) = _
      rw [DerivedCategory.Q.map_id, op_id]
    change (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        ((DerivedCategory.Q.op.prod DerivedCategory.Q).map
          (X := (op L, M)) (Y := (op L, N)) (𝟙 (op L), f)) ≫
          (schemeDerivedInternalHomResolutionIso X L N).hom =
        (schemeDerivedInternalHomResolutionIso X L M).hom ≫ DerivedCategory.Q.map h at hn₀
    rw [hQ] at hn₀
    exact hn₀
  exact tensor_naturality _ _ _ _ _ _ _ hn he

-- Elaborating the fixed sheaf tensor and localization instances needs extra heartbeats.
set_option backward.isDefEq.respectTransparency.types true in
/-- One-variable compatibility of the explicit localized identity evaluation
(Stacks, Tags 08DJ, 0A90 and 0A96). -/
theorem tensorHomEvaluation_postcomposition (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (c : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj M') :
    letI := schemeDerivedTensorMonoidal X
    let E := fun L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ↦
      ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X (homComplex (R := X.sheaf) L
          ((schemeHomKInjectiveResolution X).obj M)) L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
        schemeHomResolutionInverse X M
    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        (𝟙 (op (DerivedCategory.Q.obj L)), c.inv) ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫
        E L M = E L M' ≫ c.inv := by
  let := schemeDerivedTensorMonoidal X
  let F := (Functor.curry.obj
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).obj
      (op (DerivedCategory.Q.obj L)) ⋙ tensorRight (DerivedCategory.Q.obj L)
  let α : DerivedCategory.Q ⋙ F ⟶ DerivedCategory.Q ⋙ 𝟭 _ := {
    app := fun N ↦ evaluation X L N
    naturality := fun N N' f ↦ by
      simpa only [F, Functor.comp_map, Functor.curry_obj_obj_map, tensorRight, Functor.flip_obj_map,
        curriedTensor_map_app,
        tensorHom_id, Functor.id_map] using evaluation_chain_natural X L N N' f }
  let FF := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
    (schemeDerivedCategory X)
  let β : F ⟶ 𝟭 _ := FF.preimage α
  have hβ (N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
      β.app (DerivedCategory.Q.obj N) = evaluation X L N :=
    congrArg (fun τ ↦ τ.app N) (FF.map_preimage α)
  have h := β.naturality c.inv
  rw [hβ M', hβ M] at h
  simpa only [F, Functor.comp_map, Functor.curry_obj_obj_map, tensorRight, Functor.flip_obj_map,
        curriedTensor_map_app,
    tensorHom_id, Functor.id_map, evaluation] using h

end AlgebraicGeometry

