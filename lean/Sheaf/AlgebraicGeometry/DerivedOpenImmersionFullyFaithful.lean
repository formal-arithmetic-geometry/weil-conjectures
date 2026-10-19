/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact

/-! # Derived full faithfulness for an open immersion

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/
lem-exc-open-fully-faithful.md, node lem-exc-open-fully-faithful, order 1809.
(blueprint: lem-exc-open-fully-faithful)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For an open immersion, derived direct image followed by derived pullback is the
identity, and derived pullback kills the direct image from the closed complement.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/
lem-exc-open-fully-faithful.md, node lem-exc-open-fully-faithful, order 1809.
(blueprint: lem-exc-open-fully-faithful)

Proof:
1. The sheaf adjunction is `def-weil-pbc-inverse-image`, and its open-immersion counit is
   invertible by `lem-sc-open-immersion-pushforward-fully-faithful`. Exactness of inverse
   image (`prop-weil-pbc-inverse-image-exact`) and
   `lem-weil-pbc-exact-functor-derived-factorization` identify its derived functor with
   `mapDerivedCategory`.
2. Choose a K-injective resolution by `prop-weil-pbc-kinjective-resolutions-exist`.
   The direct image is computed on it by `lem-weil-pbc-kinjective-total-derived` and
   preserves K-injectives by `lem-weil-pbc-right-adjoint-preserves-kinjective`.
   The Hom identification `lem-weil-pbc-kinjective-hom-derived` gives naturality.
3. Apply the natural sheaf counit degreewise to the resolved complex. Localization gives
   the first natural isomorphism, independently of the resolution by the same
   K-injective computation and Hom identification.
4. The complement condition makes the ranges disjoint, so
   `lemma-openclosed-vanishing-lowerstar` gives zero after inverse image of direct image
   in every degree. Closed-immersion direct image is exact (a closed immersion is finite),
   so its termwise functor descends to the derived category. Exact inverse image and
   `lem-weil-pbc-exact-functor-derived-factorization` identify the second composite with
   this zero complex.
-/
theorem derivedOpenImmersionFullyFaithful
    {T V Z : Scheme.{u}} (g : V ⟶ T) [IsOpenImmersion g]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (h : Set.range i.base = (Set.range g.base)ᶜ) :
    Nonempty
        ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor ⋙
          (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory ≅
          𝟭 (DerivedCategory (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}))) ∧
      ∀ K : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}),
        IsZero
          (((lowerStar AddCommGrpCat.{u + 1} i).mapDerivedCategory ⋙
            (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory).obj K) := by
  sorry

end AlgebraicGeometry.Etale
