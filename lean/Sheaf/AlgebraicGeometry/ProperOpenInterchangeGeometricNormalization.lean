/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Sheaf.AlgebraicGeometry.ClopenSectionDirectImage
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs


/-!
# Refinement and base change for normalized proper/open interchange

Source: Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Refinement and base change for normalized proper/open interchange.
The ordinary and derived isomorphisms are supplied. The derived map is the
canonical rightDerivedFunctorPlusBaseChange of the ordinary map;
this theorem asserts only the indicated equalities for those fixed isomorphisms.

Source: Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F;
the corresponding numbered steps of lem-cbc-proper-open-interchange-coherence.
(blueprint: lem-cbc-normalized-proper-open-geometric-normalization)

Proof:
For a proper refinement fixing X, form the pullback of the target open. The section
of this pullback induced by (j1,id) is open and closed, has proper projection equal to
the identity on X, and its square with j1 is Cartesian. Restrict the normalized comparison
to the target open. The ordinary support equation is identity on that clopen component
and zero on the complement. Derived open restriction, the specified extension-by-zero
base-change isomorphism and clopen-component restriction identify its adjoint transpose
with the inverse of properOpenIdentification. The descended open-extension adjunction
therefore identifies it with the defined properOpenComparison. For arbitrary base change,
include both ordinary support comparisons into their common ordinary direct image. Both
pasted paths pull back the same section; the support-composition pullback equation and
ordinary mate pasting prove equality after inclusion. The inclusions are monic and inverse
image is exact, so the ordinary cube commutes before inclusion. Lift that cube by the
right-derived-unit universal property (equivalently rightDerivedFunctorPlusBaseChange_cube).
The exact comparisons are the specified extension-zero base-change maps, and the other
faces are the canonical derivedBaseChangeMapPlus maps. Their factorization equations and
the assumed canonical-map equality identify the lifted faces with the stated gamma maps.
This gives the displayed equation without any injective-preservation assumption on inverse
image. The argument never cancels a noninvertible derived exchange map.
-/
theorem properOpenInterchangeGeometricNormalization_of_normalization (Λ : Type (u + 1)) [CommRing
  Λ] [Finite Λ]
    (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ ((lowerStar (ModuleCat.{u + 1} Λ)
          p).rightDerivedFunctorPlus))
    (hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F))
    (hγ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      (γ k i r p h).hom = Functor.rightDerivedFunctorPlusBaseChange (δ k i r p h).hom) :
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (γ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom.app K =
      properOpenComparison Λ p j₁ j₂ h K) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map ((γ k i r p h).hom.app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) p₁).rightDerivedFunctorPlus).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app (((lowerStar (ModuleCat.{u + 1} Λ)
        r).rightDerivedFunctorPlus).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (γ k₁ i₁ r₁ p₁ h₁).hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K)) := by
  sorry

end AlgebraicGeometry.Etale
