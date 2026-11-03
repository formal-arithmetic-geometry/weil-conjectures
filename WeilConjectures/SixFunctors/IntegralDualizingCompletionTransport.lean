/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-! # Completion after identifying the finite dualizing reductions

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 1,
derived completeness and the inverse limit of the finite dualizing objects.
(blueprint: lem-coef-integral-dualizing-completion-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.ProEtale

private theorem conjugate_limit
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasCountableProducts C]
    {V W : ℕ → C} (t : ∀ n, V (n + 1) ⟶ V n) (e : ∀ n, V n ≅ W n)
    (L : C) (hL : IsDerivedLimit t L) :
    IsDerivedLimit (fun n ↦ (e (n + 1)).inv ≫ t n ≫ (e n).hom) L := by
  obtain ⟨p, δ, h⟩ := hL
  let q := Pi.mapIso e
  let t' := fun n ↦ (e (n + 1)).inv ≫ t n ≫ (e n).hom
  have ht : towerTransitionEndomorphism t ≫ q.hom =
      q.hom ≫ towerTransitionEndomorphism t' := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, q, Pi.mapIso_hom_π,
      towerTransitionEndomorphism, Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id, towerProductShift, Pi.lift_π_assoc,
      Pi.lift_π, Pi.mapIso_hom_π_assoc]
    simp only [t', ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨p ≫ q.hom, q.inv ≫ δ, ?_⟩
  exact (distinguished_iff_of_iso (Triangle.isoMk
    (Triangle.mk p (towerTransitionEndomorphism t) δ)
    (Triangle.mk (p ≫ q.hom) (towerTransitionEndomorphism t') (q.inv ≫ δ))
    (Iso.refl L) q q (by change p ≫ q.hom = 𝟙 L ≫ p ≫ q.hom; simp only [Category.id_comp]) ht
      (by
        change δ ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 L) = q.hom ≫ q.inv ≫ δ
        rw [(shiftFunctor C (1 : ℤ)).map_id]
        simp only [Category.comp_id, Iso.hom_inv_id_assoc]))).mp h

/-- A bounded constructible integral object is complete through its specified Roos
augmentation, and any levelwise identification of its reductions transports the limit.

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 1
(blueprint: lem-coef-integral-dualizing-completion-transport).

Proof: the integral criterion gives completeness. Choose its K-flat representative;
the representative-invariance theorem makes the canonical completion map invertible.
The augmented Roos theorem identifies its target with the derived limit of the exact
restriction of the reductions. Transport the first term of that triangle along the
completion isomorphism. Finally conjugate both product terms by the product of the
given finite-level isomorphisms. Product projections show that this conjugates 1-s
to the transition endomorphism of the displayed tower. No condition on e beyond
being an isomorphism at each level is needed: the conclusion records the conjugated
arrows explicitly, including the residue level and the zero object.
-/
theorem WeilConjectures.integralDualizing_completion_transport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K)
    (W : ℕ → DerivedCategory (AdicCompletion.Modules l E X))
    (e : ∀ n, (AdicCompletion.integralLevel l E X K n) ≅ W n) :
    (∃ (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
      (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P)
      (eP : DerivedCategory.Q.obj P ≅ K),
      IsIso (AdicCompletion.completionMap l E X K P eP)) ∧
    (letI : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)) :=
      ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ I⟩
     IsDerivedLimit
       (fun n ↦ (e (n + 1)).inv ≫ AdicCompletion.integralStep l E X K n ≫ (e n).hom)
       K) := by
  have hc' : IsDerivedComplete l E X K ∧
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) :=
    ((condensed_integral_criterion l E X K).out 0 1).mp hK
  have hc := hc'.1
  obtain ⟨P, hP, ⟨eP⟩, _⟩ := hc
  have hc := hc'.1
  have hi := (AdicCompletion.isDerivedComplete_iff l E X K P hP eP).mp hc
  refine ⟨⟨P, hP, eP, hi⟩, ?_⟩
  let : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)) :=
    ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ I⟩
  let := hi
  obtain ⟨p, δ, ht, _⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP eP
  let a := asIso (AdicCompletion.completionMap l E X K P eP)
  have hlimit : IsDerivedLimit (AdicCompletion.integralStep l E X K) K := by
    refine ⟨a.hom ≫ p, δ ≫ (shiftFunctor _ (1 : ℤ)).map a.inv, ?_⟩
    exact (distinguished_iff_of_iso (Triangle.isoMk
      (Triangle.mk (a.hom ≫ p) (towerTransitionEndomorphism
        (AdicCompletion.integralStep l E X K))
        (δ ≫ (shiftFunctor _ (1 : ℤ)).map a.inv))
      (Triangle.mk p (towerTransitionEndomorphism (AdicCompletion.integralStep l E X K)) δ)
      a (Iso.refl _) (Iso.refl _)
      (by change (a.hom ≫ p) ≫ 𝟙 _ = a.hom ≫ p; simp only [Category.comp_id])
      (by simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by
        change (δ ≫ (shiftFunctor _ (1 : ℤ)).map a.inv) ≫
          (shiftFunctor _ (1 : ℤ)).map a.hom = 𝟙 _ ≫ δ
        rw [Category.assoc, ← Functor.map_comp, a.inv_hom_id,
          (shiftFunctor _ (1 : ℤ)).map_id]
        simp only [Category.comp_id, Category.id_comp]))).mpr ht
  exact conjugate_limit (AdicCompletion.integralStep l E X K) e K hlimit
