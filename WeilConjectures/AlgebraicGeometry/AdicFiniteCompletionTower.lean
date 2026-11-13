/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.AdicFiniteStrictReductionSuccessor
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # The normalized quotient tower of completion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Pretriangulated Opposite

private theorem transportDerivedLimit
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasCountableProducts C]
    {K L : ℕᵒᵖ ⥤ C} (a : K ≅ L) {M N : C} (b : M ≅ N)
    (h : IsDerivedLimit (K := fun n : ℕ ↦ K.obj (op n))
      (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) M) :
    IsDerivedLimit (K := fun n : ℕ ↦ L.obj (op n))
      (fun n ↦ L.map (homOfLE (Nat.le_succ n)).op) N := by
  obtain ⟨p, δ, hc⟩ := h
  let d : (∏ᶜ (fun n : ℕ ↦ K.obj (op n))) ≅
      ∏ᶜ (fun n : ℕ ↦ L.obj (op n)) :=
    { hom  := Limits.Pi.map (fun n ↦ a.hom.app (op n))
      inv  := Limits.Pi.map (fun n ↦ a.inv.app (op n))
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨b.inv ≫ p ≫ d.hom, d.inv ≫ δ ≫ b.hom⟦(1 : ℤ)⟧', ?_⟩
  apply isomorphic_distinguished _ hc _
  refine Triangle.isoMk _ _ b.symm d.symm d.symm ?_ ?_ ?_
  · simp [Category.assoc]
  · exact (towerTransitionEndomorphism_natural_backward
      (fun n ↦ L.map (homOfLE (Nat.le_succ n)).op)
      (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)
      (fun n ↦ a.inv.app (op n))
      (fun n ↦ (a.inv.naturality (homOfLE (Nat.le_succ n)).op).symm)).symm
  · simp [Category.assoc, ← Functor.map_comp]

private def isoOfSuccessors
    {C : Type*} [Category C] (F : ℕᵒᵖ ⥤ C) {K : ℕ → C}
    (f : ∀ n, K (n + 1) ⟶ K n) (e : ∀ n, F.obj (op n) ≅ K n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ f n) : F ≅ Functor.ofOpSequence f := by
  let a : F ⟶ Functor.ofOpSequence f := NatTrans.ofOpSequence (fun n ↦ (e n).hom)
    (fun n ↦ by rw [Functor.ofOpSequence_map_homOfLE_succ]; exact h n)
  exact NatIso.ofComponents (fun n ↦ e n.unop) (fun g ↦ a.naturality g)

attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] adicFiniteStrictReductionLevel
  adicFiniteStrictReductionEvaluationIso derivedExtension DerivedCategory.Q
  HasDerivedCategory.standard dres change extend adicFiniteTransition

/-- The strict ordinary quotient tower on a K-flat representative computes the normalized
finite reductions, with all successor maps retained.

Source: Stacks Project, Tag 06YY (derived tensor products) and Tag 099M. -/
private theorem adicFiniteStrictReduction_comparison
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (P : Cx (constant (coefficientProEtaleModelTopology.{u, v} X) A))
    (hP : P.IsKFlatTensor)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q))
    (N : adicFiniteAmbient.{u, v} X A)
    (e : (Q (constant (coefficientProEtaleModelTopology.{u, v} X) A)).obj P ≅ N) :
    Nonempty
      ((reductionComplex (coefficientProEtaleModelTopology.{u, v} X) A J false P).asFunctor ⋙
          Q (constant (coefficientProEtaleModelTopology.{u, v} X) A) ≅
        Functor.ofOpSequence (adicFiniteTransition.{u, v} X J N)) := by
  exact ⟨isoOfSuccessors _ (adicFiniteTransition X J N)
    (fun n ↦ (adicFiniteStrictReductionLevel X A J P hP N e n).symm)
    (adicFiniteStrictReduction_successor X A J P hP hflat N e)⟩

/-- Completion is a derived limit of the actual normalized finite reductions.
Source: Stacks Project, proetale.tex, Tag 099M,
and sites-cohomology.tex, Tags 0940 and 0947. -/
theorem adicFiniteCompletion_tower
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) :
    ∃ hp : HasProduct (adicFiniteUnderlying.{u, v} X J N),
      @IsDerivedLimit _ _ _ _ _ _ _ _ hp (adicFiniteTransition.{u, v} X J N)
        ((completion (coefficientProEtaleModelTopology.{u, v} X) A J false).obj N) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T A
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  obtain ⟨RF, η, hRF, _, _, hshift, hproducts, E, ε, p, δ, _, hroos, _⟩ :=
    ringedStrictTowerHomotopyLimitIndependentCoefficients T (siteModuleRings R)
      (fun U a b ↦ @mul_comm (R.obj.obj U) _ a b)
  let := hproducts
  let := hRF
  let : (rlim R).IsRightDerivedFunctor (limitComparison R)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod R) (.up ℤ)) := (strictLimit R).universal
  let c : RF ≅ rlim R := Functor.rightDerivedUnique RF (rlim R) η
    (limitComparison R) (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod R) (.up ℤ))
  let P₀ := (Q R).objPreimage N
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  let := hq
  let e : (Q R).obj P ≅ N := asIso ((Q R).map q) ≪≫ (Q R).objObjPreimageIso N
  have hk : P.IsKFlatTensor :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
  let qp := quotientPresentation T A J false
  let : IsIso (qp.comparison.app P) := qp.laws.2.1 P hk hflat
  let Z := qp.tower.obj N
  let z : Z ≅ (TQ R).obj (reductionComplex T A J false P) :=
    qp.tower.mapIso e.symm ≪≫ asIso (qp.comparison.app P)
  obtain ⟨a⟩ := adicFiniteStrictReduction_comparison X A J P hk hflat N e
  let t : E.obj Z ≅ Functor.ofOpSequence (adicFiniteTransition X J N) :=
    E.mapIso z ≪≫ ε.app (reductionComplex T A J false P) ≪≫ a
  let hp : HasProduct (adicFiniteUnderlying X J N) :=
    (hproducts.out ℕ).has_limit (Discrete.functor (adicFiniteUnderlying X J N))
  let := hp
  refine ⟨hp, ?_⟩
  change IsDerivedLimit (adicFiniteTransition X J N) ((rlim R).obj Z)
  simpa only [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_obj] using
    transportDerivedLimit t (c.app Z) ⟨p Z, δ Z, hroos Z⟩

end AlgebraicGeometry.Scheme
