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

Source: the Weil conjectures blueprint, `det-pe-classical-derived-equivalence`,
and `definition-classical-pro-etale-sheaves` (blueprint: det-pe-classical-derived-equivalence).

The module-valued predicate and full subcategory used below are supplied by
`WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The bounded-below comparison has classical essential image and is an equivalence
onto that image, with the comparison functors as its forward and inverse functors.
The explicit counit clause is the essential-surjectivity assertion.
Source: current blueprint, classical derived-equivalence detail
(blueprint: corollary-bounded-below-classical-complexes--2).

Proof, following the node's eight steps:
1. The ringed-site categories are Grothendieck abelian
   (corollary-bounded-below-classical-complexes--2), hence admit K-injective resolutions
   (prose-03-02) computing corollary-bounded-below-classical-complexes--2.
   The module comparison theorem-classical-sheaves-essential-image--1 makes inverse image
   exact with classical essential image. Its right adjoint is additive and left exact.
2. By situation-conventions, inverse image commutes with
   cohomology and preserves lower bounds. Its image is therefore classical.
   By corollary-bounded-below-classical-complexes--2, the right derived direct
   image also preserves lower bounds, so both functors act on the stated categories.
3. Use situation-conventions and
   corollary-bounded-below-classical-complexes--2 to equip the adjoints with
   coherent shifts. By corollary-bounded-below-classical-complexes--2 the right adjoint is
   triangulated. By corollary-bounded-below-classical-complexes--2 the counit
   gives a morphism of distinguished triangles, including the connecting maps.
4. Every classical sheaf is an inverse image by theorem-classical-sheaves-essential-image--1.
   The triangle identity and the assumed unit make the counit invertible on its
   shifts, using situation-conventions, and on zero.
5. For a bounded classical object choose lower and upper bounds. Its upper
   truncation just below the lower bound has zero cohomology by
   corollary-bounded-below-classical-complexes--2 and is zero by
   corollary-bounded-below-classical-complexes--2. This starts induction on truncations.
6. The triangle of theorem-pbc-injective-acyclicity and step 3 give the ladder
   of corollary-bounded-below-classical-complexes--2. The first and third counits are
   invertible by induction and step 4. Apply corollary-bounded-below-classical-complexes--2, then
   corollary-bounded-below-classical-complexes--2. The upper bound identifies the
   final truncation with the original object, proving its counit invertible.
7. For a bounded-below classical object and a fixed degree m, choose an upper
   truncation at N at least m. By corollary-bounded-below-classical-complexes--2 it is bounded
   classical and the inclusion is a cohomology isomorphism through N, monic in N+1.
   By corollary-bounded-below-classical-complexes--2 its right derived image is an
   isomorphism on degree m. Use situation-conventions for the
   further inverse image. Counit naturality and step 6 give invertibility on degree m.
   Vary m and apply corollary-bounded-below-classical-complexes--2.
8. Restrict the adjunction to the full classical subcategory. The assumed unit,
   step 7's counit, and the unchanged triangle identities give inverse equivalences. -/
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
