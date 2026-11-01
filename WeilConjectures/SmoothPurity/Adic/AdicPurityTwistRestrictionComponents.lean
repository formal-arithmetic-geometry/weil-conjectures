/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import all WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
/-! # Components of the root-normalized restriction comparison
Source: blueprint def-coefficient-twists-detailed, finite reduction clause.
(blueprint: lem-pur-adic-twist-restriction-components).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})
section TwistReduction
variable [hInvert : ∀ x : T, Invertible (l : T.residueField x)]
include hInvert

-- Retain the established hypothesis; tensor cancellation does not require it.
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 800000 in
-- Tensor transport compares several definitionally equal coefficient-ring presentations.
/-- Objectwise balanced tensor comparison for finite scalar restriction.
Source: def-coefficient-twists-detailed, finite coefficient line and tensor powers.
(blueprint: lem-pur-adic-twist-restriction-components).
Proof: let p : R → Q be the finite quotient of the completed coefficient ring and
b the normalized first-root reduction. The positive scalar-extension powers B(k) of
b, composed with the scalar-extension embedding, satisfy the degree-zero, first-root
and successor equations, so by uniqueness they equal the prescribed root quotients.
Tensor cancellation identifies U(M ⊗_Q (Q ⊗_R L_d)) with U(M) ⊗_R L_d; compose its
inverse with the tensor presentation comparisons and with the second-factor
isomorphism M ⊗_Q (Q ⊗_R L_d) ≅ M ⊗_Q L_{d,Q} induced by B(d). On a pure tensor
x ⊗ y the cancellation formula at coefficient 1 sends it to x ⊗ (1 ⊗ y), and the
second factor to x ⊗ B(d)(1 ⊗ y), which is x ⊗ c_d(y) by the uniqueness step. No
flatness or local trivialization is used, so d = 0, the zero module, the zero
coefficient ring and the empty scheme are included. -/
theorem adicPurityTwistRestriction_component (d : ℕ)
    (M : scalarReductionTarget l E T n) :
    ∃ e : (integralSheafTwist l E T (d : ℤ)).obj
        ((scalarReductionRestriction l E T n).obj M) ≅
      (scalarReductionRestriction l E T n).obj
        ((SheafOfModules.siteSheafTensorRight
          (A := integralCoefficientCommRingSheaf l E T n)
          (finiteCoefficientTwist l E T n (d : ℤ))).obj M),
      ∀ (W : T.ProEtᵒᵖ) (x : M.val.obj W)
        (y : (integralTwistLine l E T (d : ℤ)).val.obj W),
        e.hom.val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted l E T) _ _ W x y) =
          SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W x
              ((adicPurityRootQuotients l E n T d).val.app W y) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let Q := integralCoefficientCommRingSheaf l E T n
  let p := completedIntegralCommRingProjectionUnrestricted l E T n
  let L := purTwistIntegralModule T l E
  let N := purTwistFiniteOne T l E n
  obtain ⟨b, hb⟩ := signedTwistFirstReduction l E T n
  let B := SheafOfModules.positiveComparison.{u + 1, u, u + 1} p L N b
  let c : AdicPurityRootQuotients l E n T := fun k ↦
    SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
        p (integralTwistLine l E T (k : ℤ)) ≫
      (scalarReductionRestriction l E T n).map (B k).hom
  have hc (k : ℕ) (W : T.ProEtᵒᵖ)
      (x : (integralTwistLine l E T (k : ℤ)).val.obj W) :
      (c k).val.app W x = (B k).hom.val.app W
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E T (k : ℤ)) W 1 x) := rfl
  have hnorm : IsAdicPurityRootQuotients l E n T c := by
    refine ⟨?_, ?_, ?_⟩
    · intro W a
      rw [hc]
      change (SheafOfModules.scalarExtensionUnitIso p).hom.val.app W
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          p (integralTwistLine l E T 0) W 1 a) = _
      exact (SheafOfModules.scalarExtensionUnitIso_tmul.{u + 1, u, u + 1}
        p W 1 a).trans (one_mul ((p.hom.app W).hom a))
    · intro W a x
      rw [hc]
      exact hb W (purTwistIntegralTensor T l E W a x)
    · intro k W x y
      rw [hc, hc, hc]
      exact SheafOfModules.positiveComparison_tmul.{u + 1, u, u + 1}
        p L N b k W 1 x y
  have heq : c = adicPurityRootQuotients l E n T :=
    (adicPurityRootQuotients_existsUnique l E n T).choose_spec.2 c hnorm
  let F := scalarReductionRestriction l E T n
  let K := integralTwistLine l E T (d : ℤ)
  let H := finiteCoefficientTwist l E T n (d : ℤ)
  let D := SheafOfModules.changeOfRings.{u, u + 1, u + 1} p K
  let bD : D ≅ H :=
    SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} p K ≪≫ B d
  obtain ⟨k, _, hk⟩ :=
    SheafOfModules.exists_changeOfRings_tensorCancellation_sections.{u + 1, u, u + 1} p
  let e :=
    (SheafOfModules.ScalarHomOrdinary.tensorIsoSite.{u + 1, u, u + 1} R (F.obj M) K).symm ≪≫
    (k M K).symm ≪≫ F.mapIso
      (SheafOfModules.ScalarHomOrdinary.tensorIsoSite.{u + 1, u, u + 1} Q M D ≪≫
        SheafOfModules.tensorSecondIso.{u + 1, u, u + 1} M bD)
  refine ⟨e, ?_⟩
  intro W x y
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Q).obj)
  let z := (adj.unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} p K)).app W
      ((1 : Q.obj.obj W) ⊗ₜ[R.obj.obj W, (p.hom.app W).hom] y)
  have hz : (k M K).hom.val.app W
      (SheafOfModules.ScalarHomOrdinary.pure.{u + 1, u, u + 1} Q M D W x z) =
      SheafOfModules.ScalarHomOrdinary.pure.{u + 1, u, u + 1} R (F.obj M) K W x y := by
    simpa only [SheafOfModules.ScalarHomOrdinary.pure, z, one_smul] using
      hk M K W x 1 y
  have hzi : (k M K).inv.val.app W
      (SheafOfModules.ScalarHomOrdinary.pure.{u + 1, u, u + 1} R (F.obj M) K W x y) =
      SheafOfModules.ScalarHomOrdinary.pure.{u + 1, u, u + 1} Q M D W x z := by
    rw [← hz]
    exact congrArg (fun f ↦ f.val.app W
      (SheafOfModules.ScalarHomOrdinary.pure.{u + 1, u, u + 1} Q M D W x z)) (k M K).hom_inv_id
  change (SheafOfModules.tensorSecondIso.{u + 1, u, u + 1} M bD).hom.val.app W
    ((SheafOfModules.ScalarHomOrdinary.tensorIsoSite.{u + 1, u, u + 1} Q M D).hom.val.app W
      ((k M K).inv.val.app W
        ((SheafOfModules.ScalarHomOrdinary.tensorIsoSite.{u + 1, u, u + 1}
          R (F.obj M) K).inv.val.app W
          (SheafOfModules.siteSheafTensorTmul (F.obj M) K W x y)))) = _
  erw [SheafOfModules.ScalarHomOrdinary.tensorIsoSite_inv_pure.{u + 1, u, u + 1}
      R (F.obj M) K W x y, hzi,
    SheafOfModules.ScalarHomOrdinary.tensorIsoSite_pure.{u + 1, u, u + 1} Q M D W x z,
    SheafOfModules.tensorSecondIso_hom.{u + 1, u, u + 1}]
  refine (SheafOfModules.scalarTensor_second_tmul.{u + 1, u, u + 1}
    (R := Q) M bD.hom W x z).trans ?_
  change SheafOfModules.siteSheafTensorTmul M H W x
    ((B d).hom.val.app W
      ((SheafOfModules.ScalarHomOrdinary.extensionIso.{u + 1, u, u + 1} p K).hom.val.app W z)) = _
  refine (congrArg
    (fun t ↦ SheafOfModules.siteSheafTensorTmul (A := Q) M H W x ((B d).hom.val.app W t))
    (SheafOfModules.ScalarHomOrdinary.extensionIso_unit.{u + 1, u, u + 1} p K W y)).trans ?_
  exact congrArg (SheafOfModules.siteSheafTensorTmul (A := Q) M H W x)
    ((hc d W y).symm.trans
      (congrArg (fun q : AdicPurityRootQuotients l E n T ↦ (q d).val.app W y) heq))

end TwistReduction
end WeilConjectures
