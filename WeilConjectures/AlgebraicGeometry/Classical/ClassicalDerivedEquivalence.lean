/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedCounit
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Bounded-below classical pro-étale complexes

The module-valued predicate and full subcategory used below are supplied by
`WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Assuming the derived unit of the comparison adjunction is invertible, the bounded-below
comparison functor has classical essential image, its counit is invertible on classical objects,
and it is an equivalence onto the classical full subcategory, with the comparison functors as its
forward and inverse functors. -/
theorem classicalDerivedEquivalence (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (hunit : ∀ L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit.app L)) :
    (∀ L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      ClassicalPlus X Λ
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L)) ∧
    (∀ K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
      ClassicalPlus X Λ K →
        IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.counit.app K)) ∧
    (∃ e : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ≌
          (ClassicalPlus X Λ).FullSubcategory,
      Nonempty (e.functor ⋙ (ClassicalPlus X Λ).ι ≅
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus) ∧
      Nonempty (e.inverse ≅ (ClassicalPlus X Λ).ι ⋙
        (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightDerivedFunctorPlus)) := by
  classical
  have himage := classicalDerivedImage X Λ hunit
  have hcounit := classicalDerivedCounit X Λ hunit
  refine ⟨himage, hcounit, ?_⟩
  let P := ClassicalPlus X Λ
  let L := ObjectProperty.lift P
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus himage
  let R := P.ι ⋙ (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightDerivedFunctorPlus
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus
  let radj : L ⊣ R := adj.restrictFullyFaithful
    (Functor.FullyFaithful.id _) P.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  let hu : ∀ K, IsIso (radj.unit.app K) := by
    intro K
    have hi : IsIso ((𝟭 _).map (radj.unit.app K)) := by
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      dsimp
      let : IsIso (adj.unit.app K) := hunit K
      infer_instance
    exact isIso_of_reflects_iso (radj.unit.app K) (𝟭 _)
  let hc : ∀ K, IsIso (radj.counit.app K) := by
    intro K
    have hi : IsIso (P.ι.map (radj.counit.app K)) := by
      rw [Adjunction.map_restrictFullyFaithful_counit_app]
      dsimp
      let : IsIso (adj.counit.app K.obj) := hcounit K.obj K.property
      change IsIso (𝟙 _ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.map
          (𝟙 _) ≫ adj.counit.app K.obj)
      rw [Category.id_comp]
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact hcounit K.obj K.property
    exact isIso_of_reflects_iso (radj.counit.app K) P.ι
  let e := radj.toEquivalence
  refine ⟨e, ?_, ?_⟩
  · exact ⟨ObjectProperty.liftCompιIso P
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus himage⟩
  · exact ⟨Iso.refl _⟩

end AlgebraicGeometry.ProEtale

end
