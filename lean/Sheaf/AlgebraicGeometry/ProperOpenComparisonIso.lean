/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.OpenImmersionSquare
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.AlgebraicGeometry.ProperOpenSection
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Proper pushforward of extension by zero

Source: blueprint, sec-smooth-purity/sk-def-sf-operations,
lem-weil-pbc-proper-open-comparison-iso, order 1482
(blueprint: lem-weil-pbc-proper-open-comparison-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The specified proper/open comparison is an isomorphism for every comparison datum.
Source: blueprint, sec-smooth-purity/sk-def-sf-operations,
lem-weil-pbc-proper-open-comparison-iso, order 1482
(blueprint: lem-weil-pbc-proper-open-comparison-iso).

Proof:
1. Put `M = Ru_* j₁! K`. The section of the comparison construction is clopen
   (lem-weil-pbc-proper-open-section). The specified restriction identification `θ`
   is invertible (lem-weil-pbc-proper-open-identification). Under the restriction
   unit identification, the restriction of the adjoint `α` is `θ⁻¹`: the counit
   restricts to the identity by lem-weil-pbc-extension-by-zero-adjunction, as the
   extension-by-zero presheaf of def-weil-pbc-extension-by-zero already agrees with
   the original sheaf on this restricted site. The same identities descend termwise.
2. For a geometric point outside `j₂(X)`, its fibre in `T₁` has empty intersection
   with `j₁(X)`, by the commuting triangle. Apply
   cor-cbc-derived-extension-zero-base-change to the empty-open square of
   def-cbc-open-immersion-square: the pullback of `j₁! K` to this fibre is zero.
   The empty covering forces every module sheaf on the empty scheme to be zero.
3. Apply cor-weil-pbc-geometric-fiber-finite to `f` and `j₁! K`. Extension by zero
   preserves bounded-below objects and is termwise exact by
   lem-weil-pbc-extension-by-zero-exact. Step 2 makes the derived fibre zero.
   The source also has zero stalk by lem-weil-pbc-extension-by-zero-stalks.
4. Stalks commute with cohomology by prop-weil-pbc-geometric-stalks-exact and
   lem-weil-pbc-exact-functor-bounded-below. Use
   prop-weil-pbc-inverse-image-modules-exact and
   lem-weil-pbc-geometric-point-pullback-stalk to identify the fibre computation
   with the actual module stalks. On the open use step 1; outside it use step 3.
   Thus every cohomology map of `α` is invertible on every geometric stalk.
5. Apply lemma-weil-pbc-geometric-stalk-conservative to the underlying abelian
   cohomology sheaves. Their inverse maps are module-linear: applying the original
   injective linear map to `v(λy)` and `λv(y)` gives the same result. Hence the
   cohomology maps are module isomorphisms. Finally apply
   lem-weil-pbc-derived-plus-iso-on-cohomology in the category of étale module
   sheaves on `T₂` to conclude that this specified comparison is invertible. -/
theorem isIso_properOpenComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (properOpenComparison Λ f j₁ j₂ h K) := by
  sorry

end AlgebraicGeometry.Etale
