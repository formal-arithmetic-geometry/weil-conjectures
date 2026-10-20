/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorBasic

/-! # Canonical point tensor comparison interfaces

Source: Stacks 07A4 and the recorded coefficient constructions.
(blueprint: def-sf-point-fibre-tensor-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v c e d hc he hd w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- Termwise integral sections, retaining the actual lifted coefficient action.
Source: blueprint integral fibre construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def pointIntegralComplexSections
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ :=
  (pointIntegralSections l E D.k).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The same recorded fibre with the good-complex coefficient presentation explicit.
Source: completed coefficient construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def pointIntegralTowerFibre
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    DerivedCategory (integralTowerModules l E (Spec (.of D.k))) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
  pointFibreIntegralAmbient D l E

/-- The actual endomorphism 1 minus shift defining the tensor's Roos complex.
Source: blueprint completed tensor construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def pointTensorRoosEndomorphism
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (P Q : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralOperationsTensorTowerFunctor l E
      (Spec (.of D.k))).obj (P, Q)).obj (op n))
    (integralOperationsTowerStep
      ((integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (P, Q)))

/-- The recorded exact-sections comparison, with both endpoint universes fixed.
Source: point coefficient construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def pointIntegralDerivedFactors
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    DerivedCategory.Q ⋙ pointIntegralTowerFibre D l E ≅
      pointIntegralComplexSections D l E ⋙ DerivedCategory.Q :=
  (pointIntegralSections l E D.k).mapDerivedCategoryFactors.{u + 2, u + 1}

/-- The good integral complex in the recorded ambient derived category, with its
coefficient presentation fixed before forming finite-Tor subcategory objects.
Source: completed coefficient construction
(blueprint: def-sf-point-fibre-tensor-models). -/
@[no_expose] def pointIntegralGoodDerivedObject
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k))) :=
  (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E (Spec (.of D.k)))).obj P.obj

/-- The type of maps from ordinary section tensor to the specified Roos completion.
Source: completed tensor construction (blueprint: def-sf-point-fibre-tensor-models). -/
def pointIntegralTensorCompletion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  ∀ P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
    (pointIntegralComplexSections D l E).obj P.obj ⊗
        (pointIntegralComplexSections D l E).obj Q.obj ⟶
      (pointIntegralComplexSections D l E).obj
        ((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj (P.obj, Q.obj))

/-- The canonical completed-tensor comparison target, factored to keep the
large derived-category composition opaque to later predicates.
Source: completed coefficient construction, node proof steps 3--5
(blueprint: def-sf-point-fibre-tensor-models). -/
def pointIntegralCanonicalComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (completion : pointIntegralTensorCompletion D l E)
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :=
  DerivedCategory.Q.map (completion P Q) ≫
    (pointIntegralDerivedFactors D l E).inv.app
      ((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj (P.obj, Q.obj)) ≫
    (pointIntegralTowerFibre D l E).map
      ((integralCompletedTensorComparison l E (Spec (.of D.k))).inv.app (P, Q))

/-- Every finite quotient coordinate is the tensor of the two quotient units.
Source: Stacks 07A4, 0941 and the coefficient construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def PointIntegralTensorFirst
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (completion : pointIntegralTensorCompletion D l E) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ) (p q : ℤ)
        (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
        (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))),
        ((pointIntegralSections l E D.k).map
          ((CochainComplex.mappingCocone.fst (pointTensorRoosEndomorphism D l E P.obj Q.obj) ≫
            Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l E
              (Spec (.of D.k))).obj (P.obj, Q.obj)).obj (op j)) n).f (p + q)))
          (((completion P Q).f (p + q)) ((HomologicalComplex.ιTensorObj
            ((pointIntegralComplexSections D l E).obj P.obj)
            ((pointIntegralComplexSections D l E).obj Q.obj) p q (p + q) rfl)
            (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)] y))) =
        integralOperationsTotalTensorSection l E (Spec (.of D.k)) n P.obj Q.obj p q
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
          (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.obj.X p)
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x)
          (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (Q.obj.X q)
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) 1 y)

/-- The shifted Roos coordinate of the completion map is zero.
Source: Stacks 07A4, 0941 and the coefficient construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def PointIntegralTensorSecond
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (completion : pointIntegralTensorCompletion D l E) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (k : ℤ) (z : ((pointIntegralComplexSections D l E).obj P.obj ⊗
          (pointIntegralComplexSections D l E).obj Q.obj).X k),
        ((pointIntegralSections l E D.k).map
          ((CochainComplex.mappingCocone.snd (pointTensorRoosEndomorphism D l E P.obj Q.obj)).v
            k (k + -1) rfl)) (((completion P Q).f k) z) = 0

/-- Localization of the full completion map is the inverse tensor comparison.
Source: Stacks 07A4, 0941 and the coefficient construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def PointIntegralTensorComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : PointIntegralTensorData D l hl E)
    (completion : pointIntegralTensorCompletion D l E) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (hcP : finiteTorConstructibleIntegral l E (Spec (.of D.k))
      (pointIntegralGoodDerivedObject D l E P))
    (hcQ : finiteTorConstructibleIntegral l E (Spec (.of D.k))
      (pointIntegralGoodDerivedObject D l E Q)),
    HEq
      (pointIntegralTensorComparison D l hl E S
        ⟨pointIntegralGoodDerivedObject D l E P, hcP⟩
        ⟨pointIntegralGoodDerivedObject D l E Q, hcQ⟩).inv
      ((MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).map
          (Prod.mkHom ((pointIntegralDerivedFactors D l E).hom.app P.obj)
            ((pointIntegralDerivedFactors D l E).hom.app Q.obj)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((pointIntegralComplexSections D l E).obj P.obj)
          ((pointIntegralComplexSections D l E).obj Q.obj) ≫
        pointIntegralCanonicalComparison D l E completion P Q)

/-- The unit comparison is fixed by actual constant coefficient sections.
Source: Stacks 07A4, 0941 and the coefficient construction
(blueprint: def-sf-point-fibre-tensor-models). -/
def PointIntegralTensorUnitModel
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : PointIntegralTensorData D l hl E) : Prop :=
  ∃ e :
      (pointIntegralComplexSections D l E).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).obj
          (SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).obj
        (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))),
    (∀ a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))).hom
        ((e.hom.f 0)
          ((pointIntegralSections l E D.k).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
              (SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))).inv
            (pointIntegralSectionMap l E D.k a))) = a) ∧
    HEq (S.unitIso.hom ≫ (Functor.LaxMonoidal.ε
      (DerivedCategory.Q (C := ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))))
      ((pointIntegralDerivedFactors D l E).hom.app _ ≫
        DerivedCategory.Q.map e.hom)

/-- Canonical integral normalization: the finite quotient coordinates, the zero
shifted coordinate, the localized inverse tensorator, and the constant-section unit.
Source: proof steps 2--5, Stacks 07A4 and 0941
(blueprint: def-sf-point-fibre-tensor-models). -/
structure PointIntegralTensorCanonical
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : PointIntegralTensorData D l hl E) where
  /-- The canonical completion map on good pairs. -/
  completion : pointIntegralTensorCompletion D l E
  /-- Its actual finite quotient coordinates. -/
  first : PointIntegralTensorFirst D l E completion
  /-- Its shifted coordinate. -/
  second : PointIntegralTensorSecond D l E completion
  /-- Its localization fixes the inverse comparison. -/
  comparison : PointIntegralTensorComparison D l hl E S completion
  /-- Its coefficient-unit normalization. -/
  unit_model : PointIntegralTensorUnitModel D l hl E S

end WeilConjectures
