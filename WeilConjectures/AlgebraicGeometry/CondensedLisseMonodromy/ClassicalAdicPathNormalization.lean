/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
/-! # Uniqueness of normalized classical adic paths

Source: Weil II (1.1.1) b)--d).
(blueprint: lem-a1-classical-adic-path-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
variable (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
  [IsNoetherian X] [X.IsSeparated] [∀ z : X, Invertible (l : X.residueField z)]

set_option maxHeartbeats 0 in
-- Expand the prescribed finite-level and coefficient-transport formulas.
private theorem integral_paths_unique (P Q : AdicFibrePathTransport l X (Coeff.{u} l))
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : flcFiber x ≅ flcFiber y) (E : Padic.FiniteCoefficientFields l (Coeff.{u} l))
    (F : LisseIntegralSheaf l E.val X) :
    ((P.integral E).map x y τ).hom.app F = ((Q.integral E).map x y τ).hom.app F := by
  apply ConcreteCategory.hom_ext
  intro v
  apply Concrete.limit_ext
  intro n
  have hP := P.integral_evaluation
  have hQ := Q.integral_evaluation
  unfold adicIntegralPathEvaluation at hP hQ
  obtain ⟨hP, hPv⟩ := hP x y τ E F n.unop
  obtain ⟨hQ, hQv⟩ := hQ x y τ E F n.unop
  apply (pathUnderlyingStalk y (Padic.coefficientExtensionIntegers l E.val)
    (F.obj.obj n)).injective
  exact (hPv v).trans (hQv v).symm

set_option maxHeartbeats 0 in
-- Expand the prescribed finite-level and coefficient-transport formulas.
private theorem rational_paths_unique (P Q : AdicFibrePathTransport l X (Coeff.{u} l))
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : flcFiber x ≅ flcFiber y) (E : Padic.FiniteCoefficientFields l (Coeff.{u} l))
    (F : LisseRationalSheaf l E.val X) :
    ((P.rational E).map x y τ).hom.app F = ((Q.rational E).map x y τ).hom.app F := by
  have hP := P.rational_evaluation
  have hQ := Q.rational_evaluation
  unfold adicRationalPathEvaluation at hP hQ
  apply ConcreteCategory.hom_ext
  intro v
  obtain ⟨v, rfl⟩ :=
    (eqToIso (lisseRationalFiberFunctor_obj l E.val X x F)).symm.toLinearEquiv.surjective v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
    apply (eqToIso (lisseRationalFiberFunctor_obj l E.val X y F)).toLinearEquiv.injective
    simp only [Iso.toLinearEquiv_apply, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
    rw [hP x y τ E F a z, hQ x y τ E F a z]
    rw [ConcreteCategory.congr_hom (integral_paths_unique l P Q x y τ E F.integral) z]
  | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw

private theorem cat_transport_cancel {C D : Cat.{v, w}} (h : C = D) (M : C) :
    (eqToHom h.symm).toFunctor.obj ((eqToHom h).toFunctor.obj M) = M := by
  cases h
  rfl

set_option maxHeartbeats 0 in
-- Expand the prescribed finite-level and coefficient-transport formulas.
private theorem algebraic_of_model_pair (F : LisseAlgebraicSheaf l X (Coeff.{u} l)) :
    lisseAlgebraicOfModel l X (Coeff.{u} l) (lisseAlgebraicPair l X (Coeff.{u} l) F).base
      (lisseCoefficientPairModel l X (Coeff.{u} l)
        (lisseAlgebraicPair l X (Coeff.{u} l) F)) = F := by
  unfold lisseAlgebraicOfModel lisseCoefficientPairModel
  simp only [cat_transport_cancel]
  exact (Localization.Construction.objEquiv
    (lisseCoefficientCocartesian l X (Coeff.{u} l))).right_inv F

set_option maxHeartbeats 0 in
-- Expand the prescribed finite-level and coefficient-transport formulas.
private theorem algebraic_models_paths_unique (P Q : AdicFibrePathTransport l X (Coeff.{u} l))
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : flcFiber x ≅ flcFiber y) (E : Padic.FiniteCoefficientFields l (Coeff.{u} l))
    (F : LisseRationalSheaf l E.val X) :
    (P.algebraic.map x y τ).hom.app (lisseAlgebraicOfModel l X (Coeff.{u} l) E F) =
      (Q.algebraic.map x y τ).hom.app (lisseAlgebraicOfModel l X (Coeff.{u} l) E F) := by
  have hP := P.algebraic_evaluation
  have hQ := Q.algebraic_evaluation
  unfold adicAlgebraicPathEvaluation at hP hQ
  let ex := eqToIso (lisseAlgebraicFiberFunctor_obj l X x (Coeff.{u} l)
      (lisseAlgebraicOfModel l X (Coeff.{u} l) E F)) ≪≫
    eqToIso (lisseAlgebraicFiber_ofModel l X x (Coeff.{u} l) E F)
  let ey := eqToIso (lisseAlgebraicFiberFunctor_obj l X y (Coeff.{u} l)
      (lisseAlgebraicOfModel l X (Coeff.{u} l) E F)) ≪≫
    eqToIso (lisseAlgebraicFiber_ofModel l X y (Coeff.{u} l) E F)
  apply ConcreteCategory.hom_ext
  intro v
  obtain ⟨v, rfl⟩ := ex.symm.toLinearEquiv.surjective v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
    obtain ⟨z, rfl⟩ :=
      (eqToIso (lisseRationalFiberFunctor_obj l E.val X x F)).toLinearEquiv.surjective z
    apply ey.toLinearEquiv.injective
    exact (hP x y τ E F a z).trans
      ((congrArg (fun z ↦ TensorProduct.tmul E.val a
          (eqToHom (lisseRationalFiberFunctor_obj l E.val X y F) z))
        (ConcreteCategory.congr_hom (rational_paths_unique l P Q x y τ E F) z)).trans
        (hQ x y τ E F a z).symm)
  | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw

/-- The evaluation formulas uniquely determine algebraic path transport.
Source: Weil II (1.1.1) b)--d), the integral limit and two scalar extensions.
(blueprint: lem-a1-classical-adic-path-normalization).
Proof: finite projections are jointly injective on an integral fibre, so integral
transport is determined by its underlying-set evaluation formula. Pure tensors
span a rational fibre, so its integral formula determines rational transport.
Pure tensors again determine transport on each algebraic coefficient model.
Every object of the coefficient localization is the image of its own underlying
coefficient pair; transporting that pair's rational model into its category and
back cancels. Thus the model calculation covers every algebraic sheaf. -/
theorem classical_adic_paths_equal (P Q : AdicFibrePathTransport l X (Coeff.{u} l))
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : flcFiber x ≅ flcFiber y) (F : LisseAlgebraicSheaf l X (Coeff.{u} l)) :
    (P.algebraic.map x y τ).hom.app F = (Q.algebraic.map x y τ).hom.app F := by
  rw [← algebraic_of_model_pair l F]
  exact algebraic_models_paths_unique l P Q x y τ _ _

end AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
