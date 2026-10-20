/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.ProperOpenCoefficientRefinement
public import Sheaf.Paper.ProEtaleProperOpenComparison

/-!
# Coefficient and site squares for the explicit refinement theta

Source: Stacks Project, more-etale.tex, Tag 0F7B, specialized to a proper/open
refinement; the explicit theta construction in the blueprint
(blueprint: lem-sp-refinement-coefficient-mate).

The statement combines the normalized coefficient-change square with the canonical
transport of the same proper/open arrow from the small etale to the pro-etale site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Coefficient extension and etale/pro-etale site comparison commute with the
specified proper/open refinement arrow.

Source: Stacks Project, more-etale.tex, Tag 0F7B, together with Tags 0GL6 and
09AF; the explicit three-constituent theta calculation in the blueprint
(blueprint: lem-sp-refinement-coefficient-mate).

Proof: The coefficient component is the normalized clopen-section calculation of
`AlgebraicGeometry.Etale.properOpenComparison_coefficient_refinement`; its maps are
identified on K-flat representatives by the canonical tensor/pullback comparison.
For the site component, expand `ProEtale.properOpenProEtaleIsoPlus`: the etale
proper/open map is transported by comparison pullback, the canonical direct-image
mate, and the two open extension comparisons. The three factors are exactly the
restriction, base-change, and clopen-component constituents of theta. Naturality
and cancellation of the open comparison give the displayed equality. No flatness
of the coefficient map and no cartesian hypothesis on the original refinement
square are used.
-/
theorem refinementCoefficientMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian T₁] [IsNoetherian T₂]
    (u : T₁ ⟶ T₂) [IsProper u]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ u = j₂)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ X).obj L.obj)) :
    (Etale.scalarExtension φ T₂).map
          (Etale.properOpenComparisonAmbient A u j₁ j₂ h L) ≫
        (Etale.scalarMate φ u).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj
            L.obj) ≫
        (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} B) u).map
          (Etale.properOpenCoefficientOpenIso φ j₁ L.obj).hom =
      (Etale.properOpenCoefficientOpenIso φ j₂ L.obj).hom ≫
        Etale.properOpenComparisonAmbient B u j₁ j₂ h
          { obj := (Etale.scalarExtension φ X).obj L.obj, property := hL } ∧
      (∀ {R : Type (u + 1)} [CommRing R] [Finite R]
        (K : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))),
        (ProEtale.properOpenSiteExtensionIso R j₂).hom.app K ≫
            (ProEtale.properOpenProEtaleIsoPlus R u j₁ j₂ h K).hom =
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T₂).mapDerivedCategoryPlus.map
              (Etale.properOpenComparison R u j₁ j₂ h K) ≫
            (Functor.rightDerivedFunctorPlusBaseChange
              (ProEtale.lowerStarComparisonUpperStarBaseChange u
                (ModuleCat.{u + 1} R))).app
              ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j₁).mapDerivedCategoryPlus.obj
                K) ≫
            (ProEtale.lowerStar (ModuleCat.{u + 1} R) u).rightDerivedFunctorPlus.map
              ((ProEtale.properOpenSiteExtensionIso R j₁).hom.app K)) := by
  constructor
  · exact Etale.properOpenComparison_coefficient_refinement φ u j₁ j₂ h L hL
  · intro R _ _ K
    simp only [ProEtale.properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Functor.mapIso_hom, asIso_hom,
      Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry
