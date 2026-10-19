/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.ClassicalDerivedImage
import Sheaf.AlgebraicGeometry.ClassicalDerivedCounit
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Bounded-below classical pro-étale complexes

Source: the Weil conjectures blueprint, `det-pe-classical-derived-equivalence`,
and `sk-def-pe-classical-definition` (blueprint: det-pe-classical-derived-equivalence).

The module-valued predicate and full subcategory used below are supplied by
`Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions`.
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
(blueprint: det-pe-classical-derived-equivalence).

Proof, following the node's eight steps:
1. The ringed-site categories are Grothendieck abelian
   (lem-pur-ringed-site-grothendieck-abelian), hence admit K-injective resolutions
   (lem-sfb-grothendieck-k-injective) computing def-sfb-right-derived-functor.
   The module comparison det-pe-classical-sheaves-modules makes inverse image
   exact with classical essential image. Its right adjoint is additive and left exact.
2. By lem-weil-pbc-exact-functor-bounded-below, inverse image commutes with
   cohomology and preserves lower bounds. Its image is therefore classical.
   By lem-weil-pbc-derived-functor-negative-vanishing, the right derived direct
   image also preserves lower bounds, so both functors act on the stated categories.
3. Use lem-sf-exact-functor-derived-triangulated and
   lem-weil-pbc-adjunction-shift-compatibility-unique to equip the adjoints with
   coherent shifts. By lem-sf-triangulated-right-adjoint the right adjoint is
   triangulated. By lem-weil-pbc-commshift-nattrans-triangle-morphism the counit
   gives a morphism of distinguished triangles, including the connecting maps.
4. Every classical sheaf is an inverse image by det-pe-classical-sheaves-modules.
   The triangle identity and the assumed unit make the counit invertible on its
   shifts, using lem-sf-exact-functor-derived-triangulated, and on zero.
5. For a bounded classical object choose lower and upper bounds. Its upper
   truncation just below the lower bound has zero cohomology by
   lem-weil-pbc-truncation-cohomology and is zero by
   lem-weil-pbc-derived-plus-iso-on-cohomology. This starts induction on truncations.
6. The triangle of lem-weil-pbc-truncation-triangle and step 3 give the ladder
   of lem-weil-pbc-derived-cohomology-ladder. The first and third counits are
   invertible by induction and step 4. Apply lem-weil-pbc-five-lemma, then
   lem-weil-pbc-derived-plus-iso-on-cohomology. The upper bound identifies the
   final truncation with the original object, proving its counit invertible.
7. For a bounded-below classical object and a fixed degree m, choose an upper
   truncation at N at least m. By lem-weil-pbc-truncation-cohomology it is bounded
   classical and the inclusion is a cohomology isomorphism through N, monic in N+1.
   By lem-weil-pbc-derived-functor-truncation-iso its right derived image is an
   isomorphism on degree m. Use lem-weil-pbc-exact-functor-bounded-below for the
   further inverse image. Counit naturality and step 6 give invertibility on degree m.
   Vary m and apply lem-weil-pbc-derived-plus-iso-on-cohomology.
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
