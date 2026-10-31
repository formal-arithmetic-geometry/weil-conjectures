/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTensorFiniteTransitionData
import WeilConjectures.AlgebraicGeometry.TateTensorDerivedOrdinaryNormalization
import WeilConjectures.AlgebraicGeometry.TateTensorRealizedSingleModel

/-! The finite Tate transition on ordinary root generators.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem finiteModelIso_eq_realizedShiftModel
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    (hu : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤))) :
    finiteModelIso T ell hT n d =
      realizedShiftModel T ell n (2 * (d : ℤ))
        (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (n + 1))
          (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
          (CharP.cast_eq_zero _ _) T hu d) := by
  apply Iso.ext
  rfl

attribute [local irreducible] finiteModelIso in
private theorem finiteTateTensor_transition_model_core
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          ((pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab)).homEquiv
            _ _ ((scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
              (derivedRealization T ell a).map (proTwistMap d r))) ≫
        (pbcDerivedRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
          (pbcAdicQuotient T (datum.{u} ell) b a hab)
          (pbcAdicProjection T (datum.{u} ell) a)
          (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _ ≫
        (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) a)).map
          (finiteModelIso T ell hT a d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)) (-(2 * (d : ℤ)))).hom.app _ =
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          (finiteModelIso T ell hT b d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)) (-(2 * (d : ℤ)))).hom.app _ ≫
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).map
          (finiteTateOrdinaryTransition T ell d b a hab r) := by
  have hb : IsUnit ((ell ^ (b + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (b + 1)
  have ha : IsUnit ((ell ^ (a + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (a + 1)
  have ht := finiteTateEtaleTransition_derived r
    (pow_pos (Fact.out : ell.Prime).pos _) (pow_pos (Fact.out : ell.Prime).pos _) hb ha d
  have h := realizedSemilinear_derived T ell b a hab (2 * (d : ℤ))
    (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (b + 1))
      (ell ^ (b + 1)) (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _)
      T hb d)
    (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (a + 1))
      (ell ^ (a + 1)) (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _)
      T ha d)
    (r.tensorPower d).hom (finiteTateEtaleTransition r d) ht
  rw [finiteModelIso_eq_realizedShiftModel T ell hT a d ha,
    finiteModelIso_eq_realizedShiftModel T ell hT b d]
  exact h

/-- The adjunct of the finite derived tensor reduction is a single ordinary map with
its root-power generator formula. This assertion involves no integral root tensor,
selected balancing isomorphisms, or abstract adic tower.

Source: smooth-purity transport, normalized Tate tower, Step 4, finite side of the
root-tensor calculation. (blueprint: lem-pur-tate-tensor-finite-transition)

Proof: construct the ordinary map by restriction's lax tensor structure on the
small etale site, then comparison inverse image and coefficient realization.
The ordinary generator calculation gives FiniteRootTransition, with scalar
sections mapping by the quotient and roots by r.roots. The etale derived/ordinary
normalization identifies r.tensorPower with the shifted scalar insertion of that
ordinary map. Apply exact scalar-mate transport for the two baseTateIso single
models. Its realizedShiftModel is the specified finiteModelIso, so the resulting
identity is the required completed-coefficient single-model identity. The two
lower normalization statements are separate proof obligations; the construction
and generator calculation, and this assembly, contain no holes. -/
theorem finiteTateTensor_transition_model
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    ∃ f : (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).obj
        ((realization T ell b).obj (finiteSheaf T ell b d)) ⟶
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).obj
        ((realization T ell a).obj (finiteSheaf T ell a d)),
      FiniteRootTransition T ell d b a hab r f ∧
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          ((pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab)).homEquiv
            _ _ ((scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
              (derivedRealization T ell a).map (proTwistMap d r))) ≫
        (pbcDerivedRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
          (pbcAdicQuotient T (datum.{u} ell) b a hab)
          (pbcAdicProjection T (datum.{u} ell) a)
          (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _ ≫
        (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) a)).map
          (finiteModelIso T ell hT a d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)) (-(2 * (d : ℤ)))).hom.app _ =
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          (finiteModelIso T ell hT b d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)) (-(2 * (d : ℤ)))).hom.app _ ≫
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).map f := by
  refine ⟨finiteTateOrdinaryTransition T ell d b a hab r,
    finiteTateOrdinaryTransition_generators T ell d b a hab r, ?_⟩
  exact finiteTateTensor_transition_model_core T ell hT d b a hab r

end AlgebraicGeometry.Scheme.PurityIntegralTower
