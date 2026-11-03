/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarTensorBalance
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Core normalized data for one finite completed tensor model

This isolates the scalar-extension comparison and its representative equations from
existence of the completed tensor presentation.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 03EL.
(blueprint: new-sf-adic-completed-tensor-finite-model-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

/-- All normalized finite scalar-extension data after the ordinary tensor-completion
presentation has been fixed. The completion presentation itself is deliberately not
part of this structure.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 03EL.
(blueprint: new-sf-adic-completed-tensor-finite-model-core).
-/
structure CompletedTensorFiniteModelCore
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) where
  balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  balance_sections : tensorFiniteBalanceSections l X R E balance
  kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj)
  ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ closed.tensor
  representative : tensorFiniteRepresentative l X R closed models E
    completion balance kflat ordinary

section Construction
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))

omit [∀ x : X, Invertible (l : X.residueField x)] in
private theorem extension_kflat
    (P : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((integralComplex l X R E).obj P) := by
  exact SheafOfModules.changeOfRings_isKFlat_independentCoefficients
    (coefficientMap l X R E) P (pbcExtend (coefficientMap l X R E))
    (reductionChange_obj_eq X (coefficientMap l X R E))
    (reductionChange_map_eq X (coefficientMap l X R E)) hP

private theorem balance_exists :
    ∃ balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
      ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
        coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R),
      tensorFiniteBalanceSections l X R E balance := by
  obtain ⟨balance, hbalance⟩ := pbc_tensor_balance_exists X (coefficientMap l X R E)
  refine ⟨balance, ?_⟩
  intro P Q p q U s x y
  exact hbalance P Q p q U s x y

private theorem core_of_balance
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
      ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
        coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (hbalance : tensorFiniteBalanceSections l X R E balance) :
    Nonempty (CompletedTensorFiniteModelCore l X R closed models E completion) := by
  let A := completedIntegralCommRingSheafUnrestricted l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let p := integralOperationsGoodComplex l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let q := integralOperationsGoodLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let v := (HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage p.ι
  let φ := coefficientMap l X R E
  let f := integralComplex l X R E
  let ps : ObjectProperty (CochainComplex (pbcModules X (ring l X R)) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  have hf : ∀ P, p P → ps (f.obj P) := fun P hP ↦ extension_kflat l X R E P hP.1
  let eps : DerivedCategory.Q ⋙ pbcDerivedExtend φ ⟶ f ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (pbcDerivedExtend φ) ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) (pbcExtensionCounit φ) ≫
      Functor.whiskerRight ((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft f (DerivedCategory.quotientCompQhIso _).hom
  have heps (P) : eps.app P = pbcComplexCounit φ P := rfl
  have he (P) (hP : CochainComplex.IsKFlatIndependentCoefficients P) :
      IsIso (eps.app P) := by
    rw [heps]
    dsimp only [pbcComplexCounit]
    have := pbcExtensionCounit_isIso φ P hP
    infer_instance
  let : q.IsLocalization v := integralOperationsGoodLocalization_isLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let ff := Localization.fullyFaithfulWhiskeringLeft (q.prod q)
    (v.prod v) (DerivedCategory (pbcModules X (ring l X R)))
  obtain ⟨ordinary, hordinary, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q f (pbcDerivedExtend φ) eps p ps hf ff
    (constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    completion.tensor closed.tensor completion.model models.comparison balance
    (fun P hP ↦ he P hP.1)
    (fun P Q hP hQ ↦ he _
      (coefficientTotalTensor_isKFlat.{u + 1, u + 1, u}
        (ProEt.topology X) A P Q hP.1 hQ.1))
  refine ⟨{ balance := balance
            balance_sections := hbalance
            kflat := fun P ↦ hf P.obj P.property
            ordinary := ordinary
            representative := ?_ }⟩
  intro P Q
  rcases P with ⟨P, hP⟩
  rcases Q with ⟨Q, hQ⟩
  have h := hordinary P Q hP hQ
  simpa only [heps, CoefficientTensorModels.iso, Iso.app_hom] using h

end Construction

/-- The finite scalar-extension core exists for every fixed completion presentation.
The proof is the finite cochain tensor comparison, K-flat preservation under scalar
extension, and descent of the comparison through the two good-complex localizations;
these are exactly the non-completion steps in the source argument.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 03EL.
(blueprint: new-sf-adic-completed-tensor-finite-model-core).
-/
theorem completed_tensor_finite_model_core
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    Nonempty (CompletedTensorFiniteModelCore l X R closed models E completion) := by
  obtain ⟨balance, hbalance⟩ := balance_exists l X R E
  exact core_of_balance l X R closed models E completion balance hbalance

end WeilConjectures.AdicQbarRealization
