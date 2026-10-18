/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ComparisonPullbackExact
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

set_option autoImplicit false

/-!
# Injective-resolution representative of the comparison unit

Source: literature/stacks-project/derived.tex, Lemma Tags 0DVC and 09T5
(blueprint: lem-pur-comparison-unit-injective-model).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- The unit of the bounded-below etale/pro-etale comparison, evaluated on an
injective resolution, is represented by the ordinary termwise unit followed by
that resolution. Source: literature/stacks-project/derived.tex, Lemma Tags 0DVC
and 09T5 (blueprint: lem-pur-comparison-unit-injective-model).

Proof, following the five steps of the node:
1. Put `L = finiteCoefficientComparison T Λ` and `R = finiteCoefficientDirectImage T Λ`.
   Exactness of `L` gives its termwise derived functor. Bounded below injective complexes
   are K-injective (lem-weil-pbc-bounded-below-injectives-kinjective), and `R` preserves
   K-injectivity (lem-weil-pbc-right-adjoint-preserves-kinjective). The module category
   is Grothendieck abelian (prop-pur-kinjective-resolutions-exist), hence has enough
   injectives (lem-sp-grothendieck-enough-injectives). Thus the canonical right-derived
   comparison is invertible on `J` by lem-weil-pbc-right-derived-plus-injective.
2. For a bounded below injective target `I`, compute derived Hom by homotopy Hom
   (lem-weil-pbc-kinjective-hom-derived). The termwise adjunction
   (lem-weil-pbc-termwise-adjunction-homotopy) sends a map `f : L P ⟶ I` to the ordinary
   unit followed by `R(f)`. This formula is natural in both variables.
3. For any bounded below target `N`, choose an injective resolution `r : N ⟶ I`
   (lem-sc-bounded-below-injective-resolution). Compose the preceding Hom bijection
   with the isomorphism given by the inverse of `R` derived applied to `Qr`, followed
   on the right by the right-derived comparison at `I`. For another resolution,
   the unique homotopy comparison between injective targets and naturality of the
   right-derived comparison identify the formulas. This proves independence of the
   resolution and naturality, hence gives the canonical adjunction of
   thm-weil-pbc-site-comparison with its specified comparison transformation.
4. The derived unit is the transpose of the identity of the derived inverse image.
   Evaluate this transpose with the given resolution `j`. Its homotopy representative
   is `j`, and its ordinary transpose is the termwise unit followed by `R(j)`.
   Multiplication by the derived image of `Qj` gives the displayed equality.
5. Localization makes `Qj` invertible, so its image under the derived direct image
   is invertible. The comparison at `J` is invertible by step 1. Cancelling these
   isomorphisms identifies the ordinary complex map with the derived unit, under
   exactly the identification in the node. -/
theorem comparisonUnitInjectiveModel
    (M : CochainComplex.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (J : CochainComplex.Plus (FiniteCoefficientModules T Λ))
    (j : (finiteCoefficientComparison T Λ).mapCochainComplexPlus.obj M ⟶ J)
    (hj : HomologicalComplex.quasiIso (FiniteCoefficientModules T Λ) (.up ℤ) j.hom)
    (hJ : ∀ i : ℤ, Injective (J.obj.X i)) :
    IsIso
        ((finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlus.map
          ((finiteCoefficientComparison T Λ).mapDerivedCategoryPlusFactorsh.hom.app
              ((HomotopyCategory.Plus.quotient
                  (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M) ≫
            (DerivedCategory.Plus.Qh.map
              ((HomotopyCategory.Plus.quotient (FiniteCoefficientModules T Λ)).map j)))) ∧
      IsIso
        ((finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlusUnit.app
          (((HomotopyCategory.Plus.quotient
              (FiniteCoefficientModules T Λ)).obj J))) ∧
      (finiteCoefficientDerivedComparisonAdjunction T Λ).unit.app
          (DerivedCategory.Plus.Qh.obj
            ((HomotopyCategory.Plus.quotient
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M)) ≫
        (finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlus.map
          ((finiteCoefficientComparison T Λ).mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.quotient
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M) ≫
            (DerivedCategory.Plus.Qh.map
              ((HomotopyCategory.Plus.quotient (FiniteCoefficientModules T Λ)).map j))) =
      DerivedCategory.Plus.Qh.map
          ((finiteCoefficientComparisonAdjunction T Λ).mapHomotopyCategoryPlus.unit.app
              ((HomotopyCategory.Plus.quotient
                (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj M) ≫
            (finiteCoefficientDirectImage T Λ).mapHomotopyCategoryPlus.map
              ((HomotopyCategory.Plus.quotient (FiniteCoefficientModules T Λ)).map j)) ≫
        (finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlusUnit.app
          (((HomotopyCategory.Plus.quotient
              (FiniteCoefficientModules T Λ)).obj J)) := by
  sorry

end AlgebraicGeometry.ProEtale
