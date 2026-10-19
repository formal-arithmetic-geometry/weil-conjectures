/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction
import Sheaf.AlgebraicGeometry.AbelianVariety.FrobeniusFixedTateModules
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.GroupTheory.TateModule
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-! # Arithmetic Frobenius has no fixed vector on the Jacobian Tate module

Source: blueprint/master/sec-purity-real-sheaves/sk-p-real-rankone/
lem-wf-finite-field-tate-no-fixed.md,
node lem-wf-finite-field-tate-no-fixed (blueprint: lem-wf-finite-field-tate-no-fixed).

The proof uses the geometric Jacobian Galois action, the finite-field Tate-module
fixed-vector theorem, and the finite-dimensionality supplied by the abelian-variety
Tate-module estimate. The action on points is represented explicitly by `ρ`, with
its compatibility with the canonical semilinear action.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Arithmetic Frobenius fixes no vector in the Jacobian Tate module, and its difference
from the identity is an automorphism on the rational Tate module.
Source: blueprint/master/sec-purity-real-sheaves/sk-p-real-rankone/
lem-wf-finite-field-tate-no-fixed.md,
node lem-wf-finite-field-tate-no-fixed (blueprint: lem-wf-finite-field-tate-no-fixed).

Proof plan: use `existsUnique_geometricJacobian_galoisAction` to identify the geometric
Jacobian with the base change of a Jacobian over the finite field; apply
`frobenius_fixed_tateModules_eq_zero` to its arithmetic Frobenius action; use the
finite-free Tate-module clause of `abelianVariety_estimate_of_isAlgClosed` and clear
powers of `ℓ` to obtain injectivity and then bijectivity on the rational Tate module.
-/
theorem finiteField_tate_no_fixed
    (k₀ K : Type u) [Field k₀] [Fintype k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosure k₀ K] [IsAlgClosed K]
    (C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))]
    [IsProper (C₀ ↘ Spec (.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (.of k₀))]
    (C : Scheme.{u}) [C.Over (Spec (.of K))]
    [Smooth (C ↘ Spec (.of K))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
    [IsProper (C ↘ Spec (.of K))] [GeometricallyIntegral (C ↘ Spec (.of K))]
    (p : C ⟶ C₀)
    (hC : IsPullback p (C ↘ Spec (.of K)) (C₀ ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (J : Over (Spec (.of K))) [CommGrpObj J]
    [IsJacobian (C ↘ Spec (.of K)) J]
    (φ : (picardFunctorDegree (C ↘ Spec (.of K)) 0).obj.RepresentableBy J)
    (hφ : IsPicardZeroMul (C ↘ Spec (.of K)) φ)
    (ρ : (K ≃ₐ[k₀] K) →* Multiplicative
      (AddAut (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J))))
    (hρ : ∀ (σ : K ≃ₐ[k₀] K) (x : Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)),
      ((ρ σ).toAdd x).toMul.left =
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ x.toMul.left ≫
          ((Classical.choose
            (existsUnique_geometricJacobian_galoisAction k₀ K C₀ C p hC J φ hφ).exists) σ).hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ (ℓ ∣ Fintype.card k₀)) :
    (∀ t : AddCommGroup.tateModule ℓ
        (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)),
      AddCommGroup.tateModule.congr (ρ (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ K)) t = t →
        t = 0) ∧
      ∃ e : AddCommGroup.rationalTateModule ℓ
          (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)) ≃ₗ[ℚ_[ℓ]]
          AddCommGroup.rationalTateModule ℓ
            (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)),
        ∀ v,
          e v =
            AddCommGroup.rationalTateModule.map
              ((ρ (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ K)).toAdd.toAddMonoidHom) v -
              v := by
  sorry

end AlgebraicGeometry
