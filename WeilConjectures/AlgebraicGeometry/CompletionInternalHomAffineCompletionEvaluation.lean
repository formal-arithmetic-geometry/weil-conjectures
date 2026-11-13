/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.AlgebraicGeometry.CompletionAffineSectionsCoordinates
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomAffineComponentwise
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Affine completed-Hom evaluation before tensor comparison

Source: Stacks Project, Tags 0882 and 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem completion_linearMap_ext_of_finite
    {A P T : Type u} [CommRing A] [AddCommGroup P] [Module A P] [Module.Finite A P]
    (J : Ideal A) [AddCommGroup T] [Module (AdicCompletion J A) T]
    (f g : AdicCompletion J P →ₗ[AdicCompletion J A] T)
    (h : ∀ x, f (AdicCompletion.of J P x) = g (AdicCompletion.of J P x)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite J P x
  induction z using TensorProduct.inductionOn with
  | tmul r x => simp only [AdicCompletion.ofTensorProduct_tmul, map_smul, h x]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Affine quotient evaluation is detected by the linear map on adic completions.
The supplied map sends each ordinary linear map to its adic completion. There are no
scalar extension tensor products in this comparison (Stacks, Tags 0882 and 087W). -/
theorem completion_internal_hom_affine_completion_evaluation {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X)
    (e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj))
    (he : ∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj))
    (U : X.affineOpens) :
    let A := Γ(X, U.val)
    let B := AdicCompletion (I.ideal U) A
    let N := Γ(G.obj, U.val)
    let M := Γ(F.obj, U.val)
    ∀ ε : AdicCompletion (I.ideal U) (N →ₗ[A] M) →ₗ[B]
      (AdicCompletion (I.ideal U) N →ₗ[B] AdicCompletion (I.ideal U) M),
      (∀ h : N →ₗ[A] M, ε (AdicCompletion.of (I.ideal U) _ h) =
        AdicCompletion.map (I.ideal U) h) →
    ∃ ρ : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).val.obj (op U.val) //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            ((formalCompletionSystem I (SheafOfModules.homObj
              (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f).val.app (op U.val)
              (s a) = s b} ≃ AdicCompletion (I.ideal U) (N →ₗ[A] M),
      ∀ (t : ∀ n : ℕᵒᵖ, formalModuleQuotient I (n.unop + 1) G.obj ⟶
        formalModuleQuotient I (n.unop + 1) F.obj),
        (∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
          t a ≫ (formalCompletionSystem I F.obj).map f =
            (formalCompletionSystem I G.obj).map f ≫ t b) →
        ∃ v : AdicCompletion (I.ideal U) N →ₗ[B] AdicCompletion (I.ideal U) M, ∀ s,
          (∀ n : ℕᵒᵖ, (e n).val.app (op U.val) (s.val n) =
            ((SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
              (formalModuleQuotient I (n.unop + 1) G.obj)
              (formalModuleQuotient I (n.unop + 1) F.obj)).symm (t n)).val (op U.val)) ↔
            ε (ρ s) = v := by
  classical
  let A := Γ(X, U.val)
  let J := I.ideal U
  let B := AdicCompletion J A
  let N := Γ(G.obj, U.val)
  let M := Γ(F.obj, U.val)
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have hGfinite := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X G.obj).mp G.property
  have : G.obj.IsQuasicoherent := hGfinite.1
  have : G.obj.IsFiniteType := hGfinite.2
  have : Module.Finite A N := Scheme.Modules.finite_sections_of_finiteType G.obj U.property
  have hFfinite := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X F.obj).mp F.property
  have : F.obj.IsQuasicoherent := hFfinite.1
  have : F.obj.IsFiniteType := hFfinite.2
  have : Module.Finite A M := Scheme.Modules.finite_sections_of_finiteType F.obj U.property
  have : Module.Finite A (N →ₗ[A] M) := inferInstance
  dsimp only
  intro ε hε
  obtain ⟨pN, hsurjN, hinjN, htransN, hofN, hscalarN, hlimN⟩ :=
    completion_affine_sections_coordinates I G U
  obtain ⟨pM, hsurjM, hinjM, htransM, hofM, hscalarM, hlimM⟩ :=
    completion_affine_sections_coordinates I F U
  obtain ⟨ρ, E, hEof, hE, hEvalInj⟩ :=
    completion_internal_hom_affine_componentwise I F G e he U pN pM
      hofN hofM hscalarN hscalarM
  have hεE : ε = E := completion_linearMap_ext_of_finite J ε E
    (fun h ↦ (hε h).trans (hEof h).symm)
  refine ⟨ρ, ?_⟩
  intro t ht
  have hfamily (x : AdicCompletion J N) (a b : ℕᵒᵖ) (f : a ⟶ b) :
      ((formalCompletionSystem I F.obj).map f).val.app (op U.val)
        ((t a).val.app (op U.val) (pN a x)) = (t b).val.app (op U.val) (pN b x) := by
    have h := congrArg (fun k ↦ k.val.app (op U.val) (pN a x)) (ht a b f)
    change ((formalCompletionSystem I F.obj).map f).val.app (op U.val)
      ((t a).val.app (op U.val) (pN a x)) =
      (t b).val.app (op U.val)
        (((formalCompletionSystem I G.obj).map f).val.app (op U.val) (pN a x)) at h
    rw [htransN a b f x] at h
    exact h
  choose w hw using fun x : AdicCompletion J N ↦
    hlimM (fun n ↦ (t n).val.app (op U.val) (pN n x)) (hfamily x)
  let v : AdicCompletion J N →ₗ[B] AdicCompletion J M :=
    { toFun := w
      map_add' := by
        intro x y
        apply hinjM
        intro n
        simp only [hw, map_add]
      map_smul' := by
        intro r x
        apply hinjM
        intro n
        change pM n (w (r • x)) = pM n (r • w x)
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
          (AdicCompletion.evalₐ J (n.unop + 1) r)
        rw [hw, hscalarN n r a x ha.symm, map_smul,
          hscalarM n r a (w x) ha.symm, hw] }
  have hv (n : ℕᵒᵖ) (x : AdicCompletion J N) :
      pM n (v x) = (t n).val.app (op U.val) (pN n x) := hw x n
  refine ⟨v, ?_⟩
  intro s
  rw [hεE]
  constructor
  · intro hs
    apply LinearMap.ext
    intro x
    apply hinjM
    intro n
    rw [← hE s n x, hs n, hv]
    rfl
  · intro hs n
    apply hEvalInj n
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hsurjN n x
    rw [hE s n y, hs, hv]
    rfl

end AlgebraicGeometry
