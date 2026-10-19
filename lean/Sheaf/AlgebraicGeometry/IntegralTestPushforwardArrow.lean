/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.SixFunctors.Integral.BaseChange
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.IntegralEtaleDirectImageExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Integral pushforward identifies the test-base comparison arrows

Source: Stacks Project, Tag 0F04, lemma-base-change-q-integral-top, final proof paragraph;
Tags 04C2, 0EYP and 0E46; IntegralBaseChange.lean:95-123
(blueprint: lem-sbc-integral-test-pushforward-arrow).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The two test-base comparison arrows are identified by endpoint isomorphisms natural
in the module sheaf on `T'`. The source and target functors are the existing cohomological
presentations of `p⁻¹ Rʳg_*` and `Rʳh_* e⁻¹`. Only integrality of `π` is assumed.
Source: Stacks Project, Tags 0F04 (final proof paragraph), 04C2, 0EYP and 0E46
(blueprint: lem-sbc-integral-test-pushforward-arrow).

Proof plan:
1. Use the Cartesian universal properties to construct `k : Y' ⟶ Y` with
   `k ≫ e = e' ≫ π` and `k ≫ h = h'`. Its square over `π` is Cartesian, hence
   `k` is integral (lem-sbc-integral-morphism-base-change).
2. Integral direct images `π_*` and `k_*` are exact
   (sbc-lem-integral-etale-direct-image-exact). Forgetting coefficients reflects
   exactness (lem-weil-pbc-exchange-forget-coefficients); inverse images are exact
   (prop-weil-pbc-inverse-image-modules-exact). Exact functors compute their derived
   functors (lem-weil-pbc-exact-functor-derived-functor), giving the natural comparison
   `(π_*M)[0] ≅ Rπ_*(M[0])`.
3. Integral underived exchange is invertible (lem-sbc-integral-underived-exchange).
   On bounded below K-injective representatives, derived exchange is its termwise
   map followed by `k_*` of a resolution (lem-weil-pbc-derived-exchange-termwise).
   Exactness makes this a quasi-isomorphism (lem-weil-pbc-exact-functor-bounded-below).
   Forgetting coefficients identifies and reflects the canonical arrow's invertibility
   (lem-weil-pbc-exchange-forget-coefficients).
4. Compose this exchange with the canonical derived composition isomorphisms for
   `g ∘ π` and `h ∘ k` (lem-weil-pbc-ringed-topoi-derived-pushforward-composition)
   and the comparison in step 2 to obtain natural endpoint isomorphisms.
5. Vertical pasting (sk-lem-pbc-exchange-pasting), and naturality at the comparison
   of step 2, say that the derived base-change arrows commute with these isomorphisms.
6. Apply degree-`r` cohomology. Exact inverse images identify the endpoints with the
   recorded source and target functors (lem-weil-pbc-exact-functor-bounded-below).
   The base-change maps are exactly this cohomology (sbc-def-base-change-map), and
   functoriality gives the displayed equation. Every construction is natural in `M`;
   no surjectivity, lower-degree assumption, or restriction on `r` is used. -/
theorem integralTestPushforward_baseChange_arrow
    (Λ : Type (u + 1)) [CommRing Λ]
    {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} {e' : Y' ⟶ T'} {h' : Y' ⟶ X}
    (π : T' ⟶ T) [IsIntegralHom π]
    (sq : ChosenCartesianSquare h e p g)
    (sq' : ChosenCartesianSquare h' e' p (π ≫ g)) (r : ℤ) :
    ∃ (A : lowerStar (ModuleCat.{u + 1} Λ) π ⋙ baseChangeSourceFunctor Λ p g r ≅
        baseChangeSourceFunctor Λ p (π ≫ g) r)
      (B : lowerStar (ModuleCat.{u + 1} Λ) π ⋙ baseChangeTargetFunctor Λ e h r ≅
        baseChangeTargetFunctor Λ e' h' r),
      ∀ (M : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        baseChangeHomologyMap Λ
            (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd).flip
            r ((lowerStar (ModuleCat.{u + 1} Λ) π).obj M) ≫ B.hom.app M =
          A.hom.app M ≫ baseChangeHomologyMap Λ
            (IsPullback.of_iso_pullback sq'.toCommSq sq'.isoPullback
              sq'.hom_fst sq'.hom_snd).flip r M := by
  sorry

end AlgebraicGeometry.Etale
