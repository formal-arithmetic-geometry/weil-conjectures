/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.PointDerivedHomModels
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Balanced quotient towers at the geometric point

Source: Bhatt--Scholze 3.4.10--3.4.12; the completion normalization proof, steps 1--2.
(blueprint: lem-pod-point-balanced-quotient-tower). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
attribute [-instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- Local multiplication on all quotient tensor generators.
Source: completion normalization steps 1--2
(blueprint: lem-pod-point-balanced-quotient-tower). -/
def PointQuotientTowerBalanced (C J : CochainComplex (integralTowerModules l E (Spec (.of
      D.k))) ℤ)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J) ≅
      (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
      ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of
      D.k)))) C J)) : Prop :=
  ∀ (n : ℕ) (p j : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (a b : (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n).obj.obj U)
    (x : (C.X p).val.obj U) (y : (J.X j).val.obj U),
    ((rho.hom.app (op n)).f (p + j)).val.app U
      (integralOperationsTotalTensorSection l E (Spec (.of D.k)) n C J p j U
        (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (C.X p) U a x)
        (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (J.X j) U b y)) =
      integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
        (((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E (Spec
      (.of D.k)))) C J).X (p + j)) U (a * b)
          (PointDerivedHom.totalElement.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of D.k))) C J p j U x y)

/-- The explicit inverse balancing rule on every finite quotient, compatible with transitions.
Source: Bhatt--Scholze 3.4.10--3.4.12; completion normalization steps 1--2
(blueprint: lem-pod-point-balanced-quotient-tower).

Proof: apply the integral tensor reduction tower comparison to C,J. Identify the
identity scalar-extension quotient with the ordinary quotient by multiplication.
On local generators the inverse sends (a tensor x) tensor (b tensor y) to
ab tensor (x tensor y); its inverse puts the coefficient in the second factor.
Balanced tensor relations give well-defined inverse sheaf maps. They preserve
bidegrees and hence both signed differential terms. Quotient transitions commute
with multiplication, so these maps give an isomorphism of strict towers. The
formula holds for arbitrary scalars, including zero, at n=0 and at every degree. -/
theorem point_balanced_quotient_tower (C J : CochainComplex (integralTowerModules l E (Spec (.of
      D.k))) ℤ) :
    ∃ rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J) ≅
      (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
      ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of
      D.k)))) C J), PointQuotientTowerBalanced D l E C J rho := by sorry

attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
end WeilConjectures
