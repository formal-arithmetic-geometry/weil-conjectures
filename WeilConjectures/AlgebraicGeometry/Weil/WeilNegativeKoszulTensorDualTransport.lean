/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import WeilConjectures.AlgebraicGeometry.Weil.WeilNegativeKoszulTensorRealization
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedNegativeKoszulTransitions
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.RingedNegativeKoszulFactorHomTensor
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.RingedKoszulDualizable
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! # Transport of the one-generator tensor model to the positive dual

Source: Stacks Project, algebraization.tex, Tag 0A0E; Modules on Sites, Tags 03D8, 03EK and 0GMW.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

private theorem negativeKoszulDualityAux
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections) :
    ∃ e : ∀ m : ℕ, ringedNegativeKoszul O r b m ≅
        (ringedKoszulDualTower O r b).obj (op m),
      (∀ m, ringedNegativeKoszulTransition O r b m ≫ (e m).hom =
        (e (m + 1)).hom ≫ (ringedKoszulDualTower O r b).map
          (homOfLE (Nat.le_succ m)).op) ∧
      (∀ m, ringedNegativeKoszulBasis O r b m ∅ 0 ≫ (e m).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r b m).f 0) := by
  cases r with
  | zero => exact ringedNegativeKoszulZeroDuality O b
  | succ r => exact ringedNegativeKoszulSuccDuality O r b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar realization of the tensor of negative rank-one factors is the
internal dual of the tensor of positive rank-one factors.

Source: Stacks Project, algebraization.tex, Tag 0A0E, the finite-free dual identification; Modules
on Sites, Tags 03D8, 03EK and 0GMW, tensor and inverse image of module sheaves. -/
theorem negativeKoszulTensorDualTransport
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) :
    let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
    let G := completedKoszulConstant X (intrinsicPresentationDatum d)
    let H := (G ⋙ F).mapHomologicalComplex (.up ℤ)
    let O := completedCechRing X d
    let b := fun i ↦ completedCechScalar X d (a i)
    ∃ e : ∀ m : ℕ, H.obj (finiteNegativeKoszulTensor r a m) ≅
        (ringedKoszulDualTower O r b).obj (op m),
      (∀ m, H.map (finiteNegativeKoszulTransition r a m) ≫ (e m).hom =
        (e (m + 1)).hom ≫ (ringedKoszulDualTower O r b).map
          (homOfLE (Nat.le_succ m)).op) ∧
      (∀ m, completedCechCoefficientUnit X d ≫ F.map (completedKoszulOne X
          (intrinsicPresentationDatum d)) ≫ (G ⋙ F).map
            (finiteNegativeKoszulUnitZero r a m) ≫ (e m).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r b m).f 0) := by
  obtain ⟨e, he, hu⟩ := negativeKoszulTensorRealization X d r a
  obtain ⟨f, hf, hv⟩ := negativeKoszulDualityAux (completedCechRing X d) r
    (fun i ↦ completedCechScalar X d (a i))
  refine ⟨fun m ↦ e m ≪≫ f m, ?_, ?_⟩
  · intro m
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc, he m, Category.assoc, hf m, ← Category.assoc]
  · intro m
    dsimp only [Iso.trans_hom, HomologicalComplex.comp_f]
    calc
      _ = ringedNegativeKoszulBasis (completedCechRing X d) r
          (fun i ↦ completedCechScalar X d (a i)) m ∅ 0 ≫ (f m).hom.f 0 := by
        simpa only [Category.assoc] using
          congrArg (fun g ↦ g ≫ (f m).hom.f 0) (hu m)
      _ = _ := hv m

end AlgebraicGeometry.Scheme
