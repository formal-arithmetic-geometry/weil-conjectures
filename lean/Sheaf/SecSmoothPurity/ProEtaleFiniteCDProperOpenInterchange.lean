/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange
public import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
public import Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic
public import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage

/-!
# Finite-CD proper/open interchange on the small pro-etale site

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-sf-existence/prop-exc-base-change-proper.proof.md`, Step 3;
Stacks Project, `derived.tex`, Tag 07K7
(blueprint: lem-exc-proetale-finite-cd-proper-open-interchange).

The all-sheaf finite cohomological-dimension bound makes the canonical proper/open
comparison invertible on ordinary unbounded derived categories.  Its component is
computed on K-injective complexes with injective terms by the degreewise sheaf
comparison followed by the direct image of a K-injective resolution.  The two
normalization equations below state the restriction and open-adjunction forms of
that component, including the unit that identifies the open restriction with the
identity.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Under an all-sheaf finite cohomological-dimension bound, proper direct image
commutes with extension by zero on an arbitrary open in the ordinary unbounded
small pro-etale derived categories.  The displayed comparison is the canonical map
whose representative is the degreewise proper/open sheaf comparison followed by the
termwise direct image of a K-injective resolution.

Source: blueprint `lem-exc-proetale-finite-cd-proper-open-interchange`
(blueprint: lem-exc-proetale-finite-cd-proper-open-interchange), retained repaired
proof Step 3; Stacks Project, `derived.tex`, Tag 07K7.

Proof:
1. Use the small-site Grothendieck module categories and the functorial
   K-injective resolutions from `prop-pur-kinjective-resolutions-exist`.  Represent
   `M` by a K-injective complex `J` with injective terms, choose a K-injective
   resolution `a : k_! J ⟶ I`, and use exactness of `k_!` to compute `k_! M`.
   The ordinary unbounded operations compute `Rr_* M` by `r_* J` and `Rp_* k_! M`
   by `p_* I`.
2. For every degree `s`, the Cartesian proper/open injective-acyclicity theorem
   `lem-exc-proetale-cartesian-open-injective-acyclic` gives
   `R^q p_* (k_! J^s) = 0` for `q > 0`.  Each `I^s` is also `p_*`-acyclic by
   `lem-weil-pbc-derived-functor-injective-vanishing`; no claim that `k_!` preserves
   injectives is made.
3. Apply `lem-kun-finite-cd-acyclic-complex` to `p_*`.  Its finite-CD hypothesis is
   exactly `hcd`, and its comparison identifies the termwise map `p_* a` with the
   ordinary right derived map.  Applying the specified natural sheaf comparison
   `lem-exc-proetale-proper-open-sheaf-comparison` degreewise gives the map whose
   localization is the displayed comparison.
4. A morphism of inputs is represented by a chain map between K-injective
   representatives, unique up to homotopy, by
   `lem-weil-pbc-kinjective-hom-derived`.  The corresponding comparison of the
   resolutions is unique up to homotopy; additive direct image preserves homotopies.
   Naturality of the sheaf comparison therefore proves independence of all choices
   and naturality in `M`.
5. The derived restriction comparison in
   `lem-exc-proetale-derived-open-restriction`, together with the open unit, identifies
   the restriction of the displayed map with the termwise map `r_* (k^* a)`.  The
   inverse of this map is the specified `proEtaleOpenRestrictionLambdaInverse`, so
   the first normalization equation is the unit form of this identification.
6. Under the derived adjunction `prop-exc-open-adjoint`, the adjunct of the displayed
   comparison is the inverse restriction from step 5.  The inverse adjunction
   formula is the open counit after applying `i_!`; this is the second normalization
   equation.  No quasi-compactness of `i`, boundedness, completion, constructibility,
   or etale-origin condition is used.
-/
theorem proEtaleFiniteCDProperOpenInterchange
    (A : Type u) [CommRing A] [Finite A]
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)
    [IsProper p] [IsOpenImmersion i]
    (d : ℕ)
    (hcd : ∀ (F : proEtaleRingModules V (proEtaleConstantRing V A))
      (q : ℕ), d < q →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) (q : ℤ)).obj
          ((proEtaleConstantDerivedDirectImage p A).obj
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj F)))) :
    IsIso (sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
      i p (IsPullback.of_hasPullback p i).flip) ∧
      IsIso (proEtaleOpenRestrictionLambdaInverse p i A) ∧
      ∀ M : proEtaleDerivedCategory (pullback p i) A,
        (exceptionalOpenAdjunction i A).unit.app
            ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj M) ≫
          (sfIntrinsicDerivedPullback A i).map
            ((sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
              i p (IsPullback.of_hasPullback p i).flip).app M) =
          (proEtaleOpenRestrictionLambdaInverse p i A).app M ∧
        (sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
          i p (IsPullback.of_hasPullback p i).flip).app M =
          (sfIntrinsicDerivedOpen A i).map
              ((proEtaleOpenRestrictionLambdaInverse p i A).app M) ≫
            (exceptionalOpenAdjunction i A).counit.app
              ((sfIntrinsicDerivedOpen A (pullback.fst p i) ⋙
                proEtaleConstantDerivedDirectImage p A).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
