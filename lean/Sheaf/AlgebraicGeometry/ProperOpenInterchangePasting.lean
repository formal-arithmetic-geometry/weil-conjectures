/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison


/-!
# Horizontal pasting for normalized proper/open interchange

Source: Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Horizontal pasting for normalized proper/open interchange.
The ordinary and derived isomorphisms are supplied. The derived map is the
canonical rightDerivedFunctorPlusBaseChange of the ordinary map;
this theorem asserts only the indicated equalities for those fixed isomorphisms.

Source: Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F;
the corresponding numbered steps of lem-cbc-proper-open-interchange-coherence.
(blueprint: lem-cbc-normalized-proper-open-pasting)

Proof:
The ordinary normalization determines each delta uniquely: its composite with the support
inclusion into the direct image of the composite map is prescribed, and that inclusion is
monic. For two horizontally adjacent squares, compose the two delta maps and include the
result in the direct image of the outside composite. Naturality of the support inclusions,
the two given normalizations and associativity of direct-image composition give the same
map as the outside delta. Cancel the inclusion. This proves ordinary horizontal pasting,
with the specified extension-zero composition isomorphisms.

Represent K by a bounded-below injective complex J. Choose injective resolutions
t:k!J -> I and v:l!I -> L. The canonical base-change factorization equation, together with
hgamma, says that the first derived comparison is represented by p_*t composed with delta
at J. The second comparison is represented by
q_*v composed with delta at I. Exactness of l! makes w = v composed with l!t a
quasi-isomorphism, so w is also a resolution of l!k!J. Naturality of the second ordinary
delta moves t through it. The ordinary horizontal equation just proved then identifies
the two-square representative with q_*w composed with the outside delta. The derived
comparison for the outside rectangle has exactly this representative, by the same
canonical factorization equation. The specified exact extension-zero compositors descend
from the ordinary ones. Thus these representatives give precisely the displayed equation
in D+, for every K. Their independence of resolutions follows from the canonical
right-derived-unit characterization, already imposed by hgamma.
-/
theorem properOpenInterchangeHorizontalPasting_of_normalization (Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]
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
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app (((lowerStar (ModuleCat.{u + 1} Λ)
        r).rightDerivedFunctorPlus).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus).map
          ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) := by
  sorry

end AlgebraicGeometry.Etale
