/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.ProperBaseChange.RingedCechKoszulDualKFlat
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.ProperBaseChange.RingedKoszulFactorColimit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.ProperBaseChange.RingedKoszulFiniteEvaluation
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
import WeilConjectures.ProperBaseChange.RingedAugmentedCechRestriction
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The strict Koszul completion reflector on a ringed site

Source: Stacks Project, algebraization.tex, Tags 0999, 099B and 0A0E
(blueprint: lem-weil-pbc-ringed-koszul-completion-reflector).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

set_option autoImplicit false
set_option synthInstance.maxSize 2048

private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    {N M : ringedSiteDerived O} (e : N ≅ M)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι M := by
  intro U f hf
  let H := derivedInternalHom (J.over U) (O.over U)
  exact (hN U f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e))).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end CategoryTheory
