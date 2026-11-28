/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismMultiplicationConeDescent
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical

/-! # The actual strict quotient cone augmentation

The augmentation of a complex into the Roos cone of its tower of quotients, given by the
quotient units `x ↦ 1 ⊗ x` with zero shifted coordinate.

## References

* Stacks Project, Tags 03EK, 08TC, 0941.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit
  unrestrictedIntegralTransition
  unrestrictedTowerUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{t})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem tuple_difference_zero
    {A : Type*} [Category A] [Preadditive A] [HasCountableProducts A]
    {K : ℕ → A} {P : A} (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
    (γ : ∀ n : ℕ, P ⟶ K n)
    (hγ : ∀ n : ℕ, γ (n + 1) ≫ f n = γ n) :
    Pi.lift γ ≫ towerTransitionEndomorphism f = 0 := by
  apply Pi.hom_ext
  intro n
  simp [towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hγ]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Consecutive quotient maps preserve the actual tensor unit. -/
theorem trfStrictQuotientUnit_compatible
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    unrestrictedTowerUnit l E Y P (n + 1) ≫
        (unrestrictedIntegralTransition l E Y n).app P =
      unrestrictedTowerUnit l E Y P n := by
  have hunit := unrestrictedTowerUnit_condition l E Y P
  ext i U x
  change (((unrestrictedIntegralTransition l E Y n).app P).f i).val.app U
      (((unrestrictedTowerUnit l E Y P (n + 1)).f i).val.app U x) =
    (((unrestrictedTowerUnit l E Y P n).f i).val.app U) x
  erw [hunit (n + 1) i U x, hunit n i U x]
  change (((unrestrictedIntegralTransition l E Y n).app P).f i).val.app U
      (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) U 1 x) =
    unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x
  simpa [unrestrictedIntegralTransition] using
    (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec P i U 1 x

-- Reconcile the two published scalar-restriction product presentations explicitly.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The tuple of quotient units is killed by one minus the transition shift. -/
theorem trfStrictQuotientUnit_condition
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P
          (∏ᶜ fun n : ℕ ↦ ((trfQuotientTowerFunctor l E Y).obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (f := fun n : ℕ ↦
          ((trfQuotientTowerFunctor l E Y).obj P).obj (op n))
        (fun n : ℕ ↦ unrestrictedTowerUnit l E Y P n) ≫
          trfQuotientDifference l E Y P) = 0 := by
  have hγ (n : ℕ) : unrestrictedTowerUnit l E Y P (n + 1) ≫
      integralOperationsTowerStep ((trfQuotientTowerFunctor l E Y).obj P) n =
      unrestrictedTowerUnit l E Y P n := by
    unfold integralOperationsTowerStep trfQuotientTowerFunctor
    dsimp only [CategoryTheory.Functor.flip_obj_map]
    simp only [CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ]
    exact trfStrictQuotientUnit_compatible l E Y P n
  have h : Pi.lift (f := fun n : ℕ ↦
          ((trfQuotientTowerFunctor l E Y).obj P).obj (op n))
        (fun n : ℕ ↦ unrestrictedTowerUnit l E Y P n) ≫
      trfQuotientDifference l E Y P = 0 :=
    tuple_difference_zero (A := CochainComplex (integralTowerModules l E Y) ℤ)
      (K := fun n : ℕ ↦ ((trfQuotientTowerFunctor l E Y).obj P).obj (op n)) (P := P)
      (integralOperationsTowerStep ((trfQuotientTowerFunctor l E Y).obj P))
      (fun n : ℕ ↦ unrestrictedTowerUnit l E Y P n) hγ
  rw [h]
  simp only [CochainComplex.HomComplex.δ_zero,
    CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The map into the Roos cone given by the tuple of quotient units with zero shifted
coordinate. -/
def trfStrictQuotientConeAugmentation
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    P ⟶ integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P) :=
  CochainComplex.mappingCocone.lift _
    (Pi.lift (f := fun n : ℕ ↦
          ((trfQuotientTowerFunctor l E Y).obj P).obj (op n))
        (fun n : ℕ ↦ unrestrictedTowerUnit l E Y P n)) 0
    (trfStrictQuotientUnit_condition l E Y P)

end WeilConjectures
