/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Discrete-coefficient exchange under the etale/pro-etale comparison

Source: blueprint main-20261015, sk-thm-properbasechange, pro-etale site paragraph;
Stacks Project, Tag 07A7 (blueprint: lem-weil-pbc-discrete-exchange-site-comparison).

The existing natural isomorphisms `baseChangeSourceComparisonIso` and
`baseChangeTargetComparisonIso` are the displayed composites S and T. Their definitions
include the canonical compatibility of bounded-below functors with the full derived
categories. The equality is written after that fully faithful inclusion; the last four
clauses say that both ambient endpoints belong to D+ and have classical cohomology.
The coefficient category is modules over the discrete ring, with its canonical constant
ring identifications. No continuous-function or completed coefficient ring is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparisons identify the two specified exchange mates, and both
pro-etale endpoints are bounded below and classical, for any discrete commutative ring.

Source: blueprint main-20261015, sk-thm-properbasechange.proof.md, pro-etale site paragraph;
Stacks Project, Tag 07A7 (blueprint: lem-weil-pbc-discrete-exchange-site-comparison).

Proof:
1. The chosen Cartesian identification gives an `IsPullback`. Apply the existing
   `comparison_derivedBaseChangeMap`, which allows arbitrary commutative rings, and
   use `Etale.baseChange_eq_derivedBaseChangeMapPlus` to identify the etale exchange.
2. Both etale endpoints are objects of D+. Exact comparison preserves their lower
   cohomological bounds. `classicalDerivedImage`, with the comparison unit supplied
   by `boundedBelowComparison`, makes their images classical. The canonical
   Plus-to-unbounded compatibility identifies these with the displayed images.
3. Transport each lower bound along the corresponding component of the specified
   source or target comparison isomorphism, using cohomology and invariance of zero
   objects under isomorphism. Transport classicality using
   `Scheme.proEtaleFixedClassical_iso_iff`. No exchange is inverted. -/
theorem discrete_exchange_site_comparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : ChosenCartesianSquare g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)) ≫
      (baseChangeTargetComparisonIso g' f' Λ).hom.app L =
        (baseChangeSourceComparisonIso f g Λ).hom.app L ≫
          (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj L)) ∧
    (∃ n : ℤ, DerivedCategory.IsGE
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) n) ∧
    IsClassicalComplexFor Y' Λ
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) ∧
    (∃ n : ℤ, DerivedCategory.IsGE
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) n) ∧
    IsClassicalComplexFor Y' Λ
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj L)))) := by
  have hp : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  refine ⟨?_, ?_⟩
  · simpa only [Etale.baseChange_eq_derivedBaseChangeMapPlus] using
      comparison_derivedBaseChangeMap Λ hp L
  · let A := ModuleCat.{u + 1} Λ
    let S := ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus).obj L
    let T := ((Etale.upperStar A g').mapDerivedCategoryPlus ⋙
      (Etale.lowerStar A f').rightDerivedFunctorPlus).obj L
    have hcomparison (M : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology A)) :
        (∃ n : ℤ, DerivedCategory.IsGE
          ((comparisonUpperStar A Y').mapDerivedCategory.obj M.obj) n) ∧
        IsClassicalComplexFor Y' Λ
          ((comparisonUpperStar A Y').mapDerivedCategory.obj M.obj) := by
      constructor
      · obtain ⟨n, hn⟩ := M.property
        let := hn
        exact ⟨n, (comparisonUpperStar A Y').isGE_mapDerivedCategory_obj M.obj n⟩
      · let : TopologicalSpace Λ := ⊥
        let : DiscreteTopology Λ := ⟨rfl⟩
        have hu := (boundedBelowComparison Y' Λ).1
        have hc := classicalDerivedImage Y' Λ (fun N ↦ by
          let := hu
          infer_instance) M
        exact (Scheme.proEtaleFixedClassical_iso_iff Y' Λ
          ((comparisonUpperStar A Y').mapDerivedCategoryPlusCompatibility.app M)).mp hc
    have htransport {M N : DerivedCategory
        (Sheaf (Scheme.ProEt.topology Y') A)} (e : M ≅ N)
        (hb : ∃ n : ℤ, DerivedCategory.IsGE M n)
        (hc : IsClassicalComplexFor Y' Λ M) :
        (∃ n : ℤ, DerivedCategory.IsGE N n) ∧ IsClassicalComplexFor Y' Λ N := by
      refine ⟨?_, (Scheme.proEtaleFixedClassical_iso_iff Y' Λ e).mp hc⟩
      obtain ⟨n, hn⟩ := hb
      refine ⟨n, (DerivedCategory.isGE_iff N n).mpr (fun q hq ↦ ?_)⟩
      exact ((DerivedCategory.isGE_iff M n).mp hn q hq).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)
    obtain ⟨hbS, hcS⟩ := hcomparison S
    obtain ⟨hbT, hcT⟩ := hcomparison T
    obtain ⟨hbS', hcS'⟩ := htransport ((baseChangeSourceComparisonIso f g Λ).app L) hbS hcS
    obtain ⟨hbT', hcT'⟩ := htransport ((baseChangeTargetComparisonIso g' f' Λ).app L) hbT hcT
    exact ⟨hbS', hcS', hbT', hcT'⟩

end AlgebraicGeometry.ProEtale
