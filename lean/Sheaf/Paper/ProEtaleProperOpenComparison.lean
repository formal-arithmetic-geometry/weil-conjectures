/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparisonIso
public import Sheaf.AlgebraicGeometry.ComparisonDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Comparison
import Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProperOpenComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The canonical proper-open comparison on the pro-etale site

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations, order 1484
(blueprint: lem-weil-pbc-proper-open-comparison-proetale).

The map is the transport of the specified etale map through the canonical
extension-by-zero mate and direct-image comparison. No unspecified isomorphism is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Extend the canonical sheaf extension-by-zero mate termwise to bounded below complexes.
Source: blueprint order 1484, proof paragraph 2; Stacks Tag 09AF
(blueprint: lem-weil-pbc-proper-open-comparison-proetale). -/
def properOpenSiteExtensionIso (Λ : Type (u + 1)) [CommRing Λ]
    {X T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The specified proper-open isomorphism: inverse extension comparison, comparison
pullback of the etale proper-open map, canonical direct-image mate, extension comparison.
Source: blueprint order 1484, proof paragraphs 1--3
(blueprint: lem-weil-pbc-proper-open-comparison-proetale). -/
def properOpenProEtaleIsoPlus (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ r = j₂)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L)) :=
  letI := Etale.isIso_properOpenComparison Λ r j₁ j₂ h L
  letI := isIso_comparisonDirectImagePlus Λ r
  (properOpenSiteExtensionIso Λ j₂).symm.app L ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T₂).mapDerivedCategoryPlus.mapIso
      (asIso (Etale.properOpenComparison Λ r j₁ j₂ h L)) ≪≫
    (asIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange r (ModuleCat.{u + 1} Λ)))).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj L) ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.mapIso
      ((properOpenSiteExtensionIso Λ j₁).app L)

/-- The same canonical comparison in the ambient unbounded derived category, using only
canonical compatibility isomorphisms for the bounded below inclusions.
Source: blueprint order 1484, displayed isomorphism
(blueprint: lem-weil-pbc-proper-open-comparison-proetale). -/
def properOpenProEtaleIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ r = j₂)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategory.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategory.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj)) :=
  let N := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂
  let R := (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor
  J₂.mapDerivedCategory.mapIso (N.mapDerivedCategoryPlusCompatibility.app L).symm ≪≫
    (J₂.mapDerivedCategoryPlusCompatibility.app (N.mapDerivedCategoryPlus.obj L)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (properOpenProEtaleIsoPlus Λ r j₁ j₂ h L) ≪≫
    ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.app
      (J₁.mapDerivedCategoryPlus.obj (N.mapDerivedCategoryPlus.obj L))) ≪≫
    R.mapIso (J₁.mapDerivedCategoryPlusCompatibility.app (N.mapDerivedCategoryPlus.obj L)) ≪≫
    R.mapIso (J₁.mapDerivedCategory.mapIso (N.mapDerivedCategoryPlusCompatibility.app L))

/-- The transported maps respect composition. No assertion about arbitrary pro-etale
complexes is made: the same bounded below etale `L` is used in all three terms.
Source: blueprint order 1484, final sentence
(blueprint: lem-weil-pbc-proper-open-comparison-proetale).

Proof: expand the four factors defining each comparison. The etale maps compose by
lem-weil-pbc-proper-open-comparison-composition, and the canonical direct-image mates
compose by prop-weil-pbc-comparison-direct-image. Naturality of the second mate moves
the first etale map through it. The two intermediate extension-comparison factors are
inverse and cancel. This leaves precisely the proper-open comparison for the composite,
with the fibre-product-pasting derived direct-image identification. -/
theorem properOpenProEtaleIsoPlus_comp (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ T₃ X : Scheme.{u}} [IsNoetherian T₁] [IsNoetherian T₂] [IsNoetherian T₃]
    (r : T₁ ⟶ T₂) (s : T₂ ⟶ T₃) [IsProper r] [IsProper s]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (hr : j₁ ≫ r = j₂) (hs : j₂ ≫ s = j₃)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (properOpenProEtaleIsoPlus Λ (r ≫ s) j₁ j₃
      ((Category.assoc j₁ r s).symm.trans ((congrArg (· ≫ s) hr).trans hs)) L).hom =
      (properOpenProEtaleIsoPlus Λ s j₂ j₃ hs L).hom ≫
        (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctorPlus.map
          (properOpenProEtaleIsoPlus Λ r j₁ j₂ hr L).hom ≫
        (proEtaleComparisonDirectImageCompIso Λ r s).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L)) := by
  sorry

/-- For the identity proper map the comparison is the identity under the canonical
right-derived identity identification.
Source: blueprint order 1484, final sentence
(blueprint: lem-weil-pbc-proper-open-comparison-proetale).

Proof: the etale comparison is the identity by
lem-weil-pbc-proper-open-comparison-composition. The comparison-direct-image mate is
the identity by prop-weil-pbc-comparison-direct-image. Thus the defining extension
comparison and its inverse cancel. -/
theorem properOpenProEtaleIsoPlus_id (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T X : Scheme.{u}} [IsNoetherian T] (j : X ⟶ T) [IsOpenImmersion j]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (properOpenProEtaleIsoPlus Λ (𝟙 T) j j (Category.comp_id j) L).hom ≫
        (Functor.rightDerivedFunctorPlusNatIso (lowerStarId (ModuleCat.{u + 1} Λ) T) ≪≫
          Functor.rightDerivedFunctorPlusIdIso _).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L)) =
      𝟙 _ := by
  sorry

end AlgebraicGeometry.ProEtale
