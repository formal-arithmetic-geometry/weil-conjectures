/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Proper direct images and a finite boundary

Let `b : Y ⟶ S` be proper, let `a : G ⟶ Y` be an open immersion whose closed complement
`i : Z ⟶ Y` is finite over `S`. A complex on `Y` is then controlled by its restriction to `G`
and its direct image to `S`: the part supported on `Z` is seen faithfully by `Rb_*`, since
`Rb_* i_* = R(bi)_*` and the finite direct image `(bi)_*` is exact and conservative. These are
the two boundary steps of Deligne's generic constructibility theorem
(`thm-fin-deligne-generic-open`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_isIso_rightDerivedLowerStar_map`:
  a morphism which is an isomorphism over `G` and after `Rb_*` is an isomorphism
  (`lem-fin-finite-boundary-comparison`).
- `AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar`:
  a complex which is bounded constructible over `G` and after `Rb_*` is bounded constructible
  (`lem-fin-finite-boundary-reconstruction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-fin-finite-boundary-comparison`: A proper direct image detects a comparison
off a finite boundary.

Let `b : Y ⟶ S` be proper, let `a : G ⟶ Y` be an open immersion with closed complement
`i : Z ⟶ Y`, and suppose that `i ≫ b` is finite. Let `c : K ⟶ L` be a morphism of bounded below
complexes of étale sheaves of `Λ`-modules on `Y`. If the restriction `a^* c` and the direct
image `Rb_* c` are isomorphisms, then so is `c`. -/
theorem isIso_of_isIso_upperStar_map_of_isIso_rightDerivedLowerStar_map {S Y G Z : Scheme.{u}}
    (b : Y ⟶ S) [IsProper b] (a : G ⟶ Y) [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hai : Set.range i = (Set.range a)ᶜ) [IsFinite (i ≫ b)]
    {K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (c : K ⟶ L) (hK : ∃ n : ℤ, K.IsGE n) (hL : ∃ n : ℤ, L.IsGE n)
    (ha : IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.map c))
    (hb : IsIso ((R((b)_*[ModuleCat.{u + 1} Λ])).map c)) :
    IsIso c :=
  sorry

/-- Blueprint `lem-fin-finite-boundary-reconstruction`: Recovering constructibility at a finite
boundary.

Let `b : Y ⟶ S` be a proper morphism between schemes of finite type over a field `k`, and let
`Λ` be a finite ring whose exponent is invertible on `S`. Let `a : G ⟶ Y` be an open immersion
with closed complement `i : Z ⟶ Y`, and assume that `i ≫ b` is finite. If `K` is a bounded below
complex on `Y` such that `a^* K` and `Rb_* K` are bounded constructible, then `K` is bounded
constructible. -/
theorem boundedConstructible_of_upperStar_of_rightDerivedLowerStar [Finite Λ] {k : Type u}
    [Field k] {S Y G Z : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (b : Y ⟶ S) [IsProper b] (a : G ⟶ Y)
    [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i] (hai : Set.range i = (Set.range a)ᶜ)
    [IsFinite (i ≫ b)]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∃ n : ℤ, K.IsGE n)
    (ha : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) G
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K))
    (hb : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K :=
  sorry

end Etale

end AlgebraicGeometry
