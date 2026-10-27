/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TateTensorFiniteTransitionData

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

/-- The adjunct of the finite derived tensor reduction is a single ordinary map with
its root-power generator formula. This assertion involves no integral root tensor,
selected balancing isomorphisms, or abstract adic tower.

Source: smooth-purity transport, normalized Tate tower, Step 4, finite side of the
root-tensor calculation. (blueprint: lem-pur-tate-tensor-finite-transition)

Proof: use finiteModelIso to replace each shifted ordered derived tensor by its
ordinary finite root tensor in degree -2d. Exact restriction commutes with this
single embedding. Fullness of the single embedding gives the ordinary map f.
At degree zero the scalar mate is multiplication of coefficient sections. At one
root factor, derived_normalization identifies the derived comparison with the
single of sheafIso, and generators identifies its adjunct on a scalar/root tensor.
Induct on d using tensorPowerStep: the normalized scalar tensorator and the shift
comparison act on pure tensors by balancing, so the formula tensors factor by
factor, with no sign since every shift is even. The site/scalar comparison and
scalarComparison are mates of the identity on the underlying scalar restriction;
thus their adjuncts preserve the same sheafification generators. This gives the
displayed formula with q(t) and phi(s). Exact realization and restriction transport
this computation to the completed coefficient category. Sheafification extends it
to every section. Equal indices, d=0 and the empty scheme use these same formulas. -/
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
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).map f := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
