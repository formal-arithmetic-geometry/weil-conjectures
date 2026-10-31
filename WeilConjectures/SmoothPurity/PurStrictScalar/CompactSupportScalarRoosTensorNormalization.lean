/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations
public import WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
import all WeilConjectures.CategoryTheory.RoosTensor.RoosTensorNormalization

/-! # Tensor normalization for unit-normalized support Roos comparisons

Source: Stacks Tags 03EK and 0941.
(blueprint: lem-pur-compact-support-scalar-roos-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme hiding Modules
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
attribute [local irreducible] constantMap completedCoefficientMap roosAdditiveComparison

/-- The canonical coordinate tensor comparison represents the actual derived
tensor/limit map under any two unit-normalized Roos presentations, and carries
strict compatible augmentations to their coordinatewise tensor extensions.
Source: Stacks Tags 03EK, 0941.
(blueprint: lem-pur-compact-support-scalar-roos-tensor-normalization).
Proof: the constant scalar tensor and tower tensor are exact, and scalarLimitTensor
has its recorded exact square. Rewrite the supplied comparison as the canonical
roosAdditiveComparison. The generic roosTensorNormalization theorem, applied to
the two supplied unit equations, gives the derived tensor/limit equality. For a
compatible family, comparison_augmentation gives the mapped compatibility equations
and equality of the augmentations, since both have coordinates (0,F(a)). -/
theorem scalarRoosTensorNormalization_of_units (W : Scheme.{u})
    (κE : roosF (A := Modules
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q ⋙ scalarLimit l E W)
    (κF : roosF (A := Modules
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q ⋙ scalarLimit l F W)
    (hE : ∀ K : CochainComplex (Towers
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ,
      DerivedCategory.Q.map (roosι K) ≫ κE.hom.app K =
        DerivedCategory.Q.map
          (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
            HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        Functor.rightDerivedFunctorUnitQ
          (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
            Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) K)
    (hF : ∀ K : CochainComplex (Towers
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) ℤ,
      DerivedCategory.Q.map (roosι K) ≫ κF.hom.app K =
        DerivedCategory.Q.map
          (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
            HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        Functor.rightDerivedFunctorUnitQ
          (lim : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W ⥤
            Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) K)
    (K : CochainComplex (Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
    (θ : ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).obj
        (roosF.obj K) ≅
      roosF.obj (((tensor l E F i W).mapHomologicalComplex (.up ℤ)).obj K))
    (hθ : θ.hom = roosAdditiveComparison (pbcExtend (constantMap l E F i W)) K) :
    (baseTensor l E F i W).map (κE.hom.app K) ≫
        (scalarLimitTensor l E F i W).hom.app (DerivedCategory.Q.obj K) =
      baseTensorCounit l E F i W (roosF.obj K) ≫
        DerivedCategory.Q.map θ.hom ≫
        κF.hom.app
          (((tensor l E F i W).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (scalarLimit l F W).map
          ((tensor l E F i W).mapDerivedCategoryFactors.inv.app K) ∧
    (∀ (P : CochainComplex
        (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) ℤ)
      (a : ∀ n : ℕ, P ⟶ K.asFunctor.obj (op n))
      (ha : ∀ n : ℕ, a (n + 1) ≫
        K.asFunctor.map (homOfLE (Nat.le_succ n)).op = a n),
      ∃ h : ∀ n : ℕ,
        ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map
            (a (n + 1)) ≫
          (((tensor l E F i W).mapHomologicalComplex (.up ℤ)).obj K).asFunctor.map
            (homOfLE (Nat.le_succ n)).op =
          ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map (a n),
        ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map
            (roosAugment a ha) ≫ θ.hom =
          roosAugment (fun n : ℕ ↦
            ((pbcExtend (constantMap l E F i W)).mapHomologicalComplex (.up ℤ)).map (a n)) h) := by
  let G := pbcExtend (constantMap l E F i W)
  have := (tensor_exact l E F i W).1
  have := (tensor_exact l E F i W).2
  have := (scalarLimitTensor_exact l E F i W).1
  have := (scalarLimitTensor_exact l E F i W).2.1
  have := (scalarLimitTensor_exact l E F i W).2.2.1
  have := (scalarLimitTensor_exact l E F i W).2.2.2
  constructor
  · rw [hθ]
    exact CategoryTheory.RoosTensor.roosTensorNormalization G
      κE κF
      hE
      hF K
  · intro P a ha
    rw [hθ]
    exact CategoryTheory.RoosTensor.comparison_augmentation G K P a ha

end WeilConjectures.PurStrictScalar
