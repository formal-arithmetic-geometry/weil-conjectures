/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility
import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Site comparison respects the normalized open base-change map

Source: Stacks Project, Tag 03S6 (`lemma-shriek-base-change`), with the normalized
comparison of Tag 09AF and pullback coherence of Tag 099R (blueprint:
`lem-fix-site-open-exchange`).  The theorem below states the ordinary derived
comparison equation for every bounded-below etale complex and arbitrary bottom
map `g`; its proof is postponed at stage 2.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The derived site comparison for extension by zero, `c_j : N_X j_!^et ≅ j_!^proet N_U`,
the degreewise extension of the sheaf comparison of
lem-cbc-proetale-extension-zero-comparison.  It is the same construction as the upstream
`mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso`, whose module cannot be
imported together with this item's side imports.
Source: Stacks Tag 09AF (`lemma-jshriek-comparison`), blueprint
`lem-fix-site-open-exchange`. -/
noncomputable def fixSiteOpenComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The inverse-image comparison, oriented as `rho_u : u_proet⁻¹ N_V ≅
N_T u_et⁻¹`: degreewise `comparisonUpperStarCompUpperStarIso`, the inverse of the canonical
comparison of lem-weil-pbc-comparison-pullback.  It is the same construction as the
upstream `mapDerivedCategoryComparisonUpperStarCompUpperStarIso`, whose module cannot be
imported together with this item's side imports.
Source: Stacks Tag 099R; blueprint `lem-fix-site-open-exchange`. -/
noncomputable def fixSitePullbackComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (u : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) u).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) u) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The normalized site-comparison/open-exchange equation.
Source: Stacks Tag 03S6 (`lemma-shriek-base-change`), Tags 09AF and 099R
(blueprint: lem-fix-site-open-exchange).

For each bounded-below `K`, the left side is `g⁻¹(c_j)`, then the actual pro-etale
base-change isomorphism `e_j^proet`, then `j'_!(rho_h)`.  The right side is `rho_g`,
then `N_X'` of the actual etale base-change isomorphism `e_j^et`, then `c_{j'}`.  The
cartesian square is the chosen one of `sq`, read as an `IsPullback` witness.  The
inverse-unit normalization of `c_j` asserted by the node is the published statement
`openComparison_unit_normalization` (lem-sf-open-comparison-unit-normalization) about
the same sheaf comparison `openImmersionLowerShriekComparisonUpperStarIso`.

Proof plan (the node's steps):
1. `c_j`, `c_{j'}` are the degreewise extensions of the natural sheaf comparison
   (lem-cbc-proetale-extension-zero-comparison), exact functors by
   lem-weil-pbc-extension-by-zero-exact and lem-cbc-proetale-extension-zero; `rho_u`
   is the inverse of the canonical comparison of lem-weil-pbc-comparison-pullback.
2. Every arrow is the image of a degreewise map of complexes, so it suffices to treat
   one etale module sheaf `F`.  The inverse of `e_j^et` is the `j'_! ⊣ j'⁻¹` transpose of
   `s_g ∘ h⁻¹(eta^et_j)` (lem-cbc-derived-extension-zero-base-change-underived-compatibility);
   the inverse of `e_j^proet` is the transpose of `sigma ∘ h⁻¹(eta^proet_j)`
   (lem-cbc-finite-open-exchange-scalars with `B = C = Λ`, `a = id`).
3. The unit normalization (lem-sf-open-comparison-unit-normalization) gives the transpose
   of `c_j⁻¹` as `rho_j⁻¹ ∘ N_U(eta^et_j)`, and likewise for `j'`.
4. Compute the `j'_!`-transposes of the inverses of both sides:
   `[sigma ∘ h⁻¹(a_j) ∘ a_h] ∘ N_{U'}h⁻¹(eta^et_j)` and
   `[j'⁻¹(a_g) ∘ a_{j'} ∘ N_{U'}(s_g)] ∘ N_{U'}h⁻¹(eta^et_j)` (def-weil-pbc-adjunction-mate).
5. The two brackets agree by the composite and cartesian-square compatibility of the
   canonical comparison (lem-weil-pbc-comparison-pullback, def-weil-pbc-cartesian-square);
   so the inverses, hence both sides, are equal degreewise and in the derived category,
   naturally in `K`.
6. The identity square, an empty open, the zero complex and the zero ring are included;
   no hypothesis on `g` is used beyond the open-immersion square. -/
theorem fixSiteOpenExchange (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare gU j' j g)
    (K : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.map
        ((fixSiteOpenComparison Λ j).hom.app
          (DerivedCategory.Plus.ι.obj K)) ≫
      (ordinaryOpenExtensionBaseChangeIso Λ gU j' j g
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategory.map
        ((fixSitePullbackComparison Λ gU).hom.app
          (DerivedCategory.Plus.ι.obj K)) =
    (fixSitePullbackComparison Λ g).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.extensionZeroBaseChangeDerivedPlusIso Λ
            (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst
              sq.hom_snd)).hom.app K)) ≫
      (fixSiteOpenComparison Λ j').hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) gU).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
