/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.PointBalancedQuotientTower
public import Sheaf.Paper.PointFibreDerivedTensorModels

/-! # Sections balancing into the fixed tensor completion

Source: Stacks 07A4 and 0941; completion normalization proof step 6.
(blueprint: lem-pod-point-sections-balancing-completion). -/

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
/-- The strict sections-completion equation for the recorded cone and unit.
Source: completion normalization step 6, Stacks 07A4 and 0941
(blueprint: lem-pod-point-sections-balancing-completion). -/
def PointSectionsCompletionEquation
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l
      E))) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
      ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of
      D.k)))) C.obj J.obj))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj)
    (beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶ (pointIntegralComplexSections D l
      E).obj ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of D.k)))) C.obj J.obj)) : Prop :=
  beta ≫ (pointIntegralComplexSections D l E).map ((completedScalarIdentityUnit l E (Spec (.of
      D.k))).app
        ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E (Spec
      (.of D.k)))) C.obj J.obj) ≫ (integralOperationsRoosFunctor.mapIso rho).inv) =
      (MonoidalCategory.tensor (CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionIntegers l E))) ℤ)).map
        (X := (P, (pointIntegralComplexSections D l E).obj J.obj)) (Y :=
      ((pointIntegralComplexSections D l E).obj C.obj, (pointIntegralComplexSections D l E).obj
      J.obj))
        (Prod.mkHom eta (𝟙 ((pointIntegralComplexSections D l E).obj J.obj))) ≫
      canonical.completion C J

/-- Generator normalization together with the strict completion equation.
Source: completion normalization step 6
(blueprint: lem-pod-point-sections-balancing-completion). -/
def PointSectionsBalancingProperty
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l
      E))) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
      ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of
      D.k)))) C.obj J.obj))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj)
    (beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶ (pointIntegralComplexSections D l
      E).obj ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of D.k)))) C.obj J.obj)) : Prop :=
  (∀ (p j : ℤ) (x : P.X p) (h : ((pointIntegralComplexSections D l E).obj J.obj).X j),
        (beta.f (p + j)).hom
          ((HomologicalComplex.ιTensorObj P ((pointIntegralComplexSections D l E).obj J.obj) p j (p
      + j) rfl).hom
            (x ⊗ₜ[(ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))] h)) =
        PointDerivedHom.totalElement.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of D.k))) C.obj J.obj p j
          (op (PointDerivedHom.finalObject D.k)) ((eta.f p).hom x) h) ∧
    PointSectionsCompletionEquation D l E hl S canonical P C J rho eta beta

/-- Sections balancing commutes with the specified two-coordinate Roos augmentation.
Source: Stacks 07A4 and 0941; completion normalization step 6
(blueprint: lem-pod-point-sections-balancing-completion).

Proof: the lax tensor comparison for final-object sections sends x tensor y to
the corresponding section of the sheaf tensor. Apply it to the signed total
complex and precompose with eta tensor identity. It commutes with differentials
by the signed total differential formula. This gives beta and its generator rule.
For the asserted chain equation, compose with the quotient projections of the
Roos cone. The balancing formula identifies each resulting generator with the
quotient tensor of the two unit sections, exactly canonical.first. The shifted
projection is zero on both sides by the identity augmentation coordinate and
canonical.second. Sections preserve products and biproducts, so these projections
jointly determine each degree component. Tensor generators and total coproduct
injections then prove equality of chain maps. No quasi-isomorphism of eta or
boundedness of P is needed for this chain-level identity. -/
theorem point_sections_balancing_completion
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l
      E))) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
      ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of
      D.k)))) C.obj J.obj))
    (hbal : PointQuotientTowerBalanced D l E C.obj J.obj rho)
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj) :
    ∃ beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶ (pointIntegralComplexSections D l
      E).obj ((PointDerivedHom.total.{u, u} D.k (completedIntegralCommRingSheafUnrestricted l E
      (Spec (.of D.k)))) C.obj J.obj),
      PointSectionsBalancingProperty D l E hl S canonical P C J rho eta beta := by sorry

attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
end WeilConjectures
