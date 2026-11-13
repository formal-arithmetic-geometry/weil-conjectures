/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Bounded-below pro-etale comparison

Source: Stacks Tags 099V, 099W and 03Q6.

The affine formula is stated on bounded-below injective representatives. The source
complex of its comparison map is the termwise filtered colimit, which represents the
filtered derived colimit because filtered colimits of modules are exact.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The canonical global-sections comparison, obtained by applying derived etale sections
to the derived adjunction unit and then the Leray isomorphism. No finiteness or commutativity
is required of the coefficient ring. Source: Stacks 099V and 099W. -/
noncomputable def boundedBelowComparisonGlobalSections (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] :
    DerivedCategory.Plus.ι ⋙ Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.ι ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X :=
  let L := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus
  let R := comparisonLowerStar (ModuleCat.{u + 1} Λ) X
  let Γ := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  (Functor.leftUnitor (DerivedCategory.Plus.ι ⋙ Γ)).inv ≫
    Functor.whiskerRight (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit
      (DerivedCategory.Plus.ι ⋙ Γ) ≫
    (Functor.associator L R.rightDerivedFunctorPlus (DerivedCategory.Plus.ι ⋙ Γ)).hom ≫
    Functor.whiskerLeft L
      ((Functor.associator R.rightDerivedFunctorPlus DerivedCategory.Plus.ι Γ).inv ≫
        Functor.whiskerRight R.rightDerivedFunctorPlusCompatibility.hom Γ ≫
        (Functor.associator DerivedCategory.Plus.ι R.rightDerivedFunctor Γ).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (comparisonLowerStarCompRightDerivedGlobalSectionsIso
            (ModuleCat.{u + 1} Λ) X).hom)

/-- The derived unit, full faithfulness on D+ and the canonical global-sections comparison.
Source: Stacks 099V and 099W. -/
theorem boundedBelowComparison (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] :
    IsIso (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit ∧
      Nonempty (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.FullyFaithful ∧
      IsIso (boundedBelowComparisonGlobalSections X Λ) := by
  have hu := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) X
  have hunit : IsIso (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
        (fun _ _ ↦ inferInstance)
        (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective
          (ModuleCat.{u + 1} Λ) X I) K
  refine ⟨hunit, ⟨Adjunction.fullyFaithfulLOfIsIsoUnit
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus⟩, ?_⟩
  unfold boundedBelowComparisonGlobalSections
  infer_instance

end AlgebraicGeometry.ProEtale
