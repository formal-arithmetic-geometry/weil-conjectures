/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NA
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Normalized composition of bounded-below étale direct images

Source: Stacks Project, sites-cohomology.tex, Tag 0D6E,
lemma-derived-pushforward-composition; bounded-below constant-coefficient specialization
(blueprint: lem-cbc-etale-derived-direct-image-coherence).

The comparison is oriented from the composite pushforward to the iterated pushforward.
Named composite morphisms avoid hiding scheme-category associators and identity equalities.
The categories are the bounded-below subcategories of `Etale.DerivedCategoryModule`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical normalized compositor, identity comparisons, and their coherence.

Source: Stacks Project, Tag 0D6E, lemma-derived-pushforward-composition
(blueprint: lem-cbc-etale-derived-direct-image-coherence).

Proof plan: (1) construct the underived comparisons from fibre-product associativity and
identity isomorphisms (`lowerStarComp.inv`, `lowerStarId.hom`); restriction makes them linear
and natural. (2) The fibre-product universal property proves their associativity and unit
laws. (3) Exact constant-coefficient inverse image is left adjoint to direct image, so direct
image preserves injectives; additivity preserves the lower bound. (4) On injective complexes
form the normalized compositor by the three derived-unit computation isomorphisms displayed
below. (5) Enough injectives gives an injective representative for every bounded-below
object. The K-injective Hom bijection proves independence of representatives, naturality,
and uniqueness by conjugation. (6) Apply the same construction to the identity comparison.
(7) Expand both associativity paths on an injective representative and cancel the computation
maps; the underived associativity law identifies them. Equivalently use
`rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc` for the inverse canonical comparisons.
(8) Expand each unit composite, cancel the computation maps, and apply the underived unit
law. Naturality and injective representatives extend all equalities to every object.
-/
theorem exists_normalizedDerivedDirectImageCoherence (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (d : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        (fg : X ⟶ Z) (w : fg = f ≫ g),
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) fg ≅
          rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
            rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g)
      (e : ∀ T : Scheme.{u},
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (𝟙 T) ≅
          𝟭 (DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))),
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
          (w : fg = f ≫ g)
          (I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (∀ n : ℤ, Injective (I.obj.as.X n)) →
        (lowerStar (ModuleCat.{u + 1} Λ) fg).rightDerivedFunctorPlusUnit.app I ≫
            (d f g fg w).hom.app (DerivedCategory.Plus.Qh.obj I) =
          DerivedCategory.Plus.Qh.map
              ((NatTrans.mapHomotopyCategoryPlus
                (lowerStarComp (ModuleCat.{u + 1} Λ) f g fg w).inv).app I) ≫
            (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusUnit.app
              ((lowerStar (ModuleCat.{u + 1} Λ) f).mapHomotopyCategoryPlus.obj I) ≫
            (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g).map
              ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusUnit.app I)) ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
          (w : fg = f ≫ g)
          (c : rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) fg ⟶
            rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
              rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g),
        (∀ I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (∀ n : ℤ, Injective (I.obj.as.X n)) →
          c.app (DerivedCategory.Plus.Qh.obj I) =
            (d f g fg w).hom.app (DerivedCategory.Plus.Qh.obj I)) →
        c = (d f g fg w).hom) ∧
      (∀ (T : Scheme.{u})
          (I : HomotopyCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (∀ n : ℤ, Injective (I.obj.as.X n)) →
        (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 T)).rightDerivedFunctorPlusUnit.app I ≫
            (e T).hom.app (DerivedCategory.Plus.Qh.obj I) =
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus
              (lowerStarId (ModuleCat.{u + 1} Λ) T).hom).app I)) ∧
      (∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
        (d (f ≫ g) h ((f ≫ g) ≫ h) rfl).hom ≫
            Functor.whiskerRight (d f g (f ≫ g) rfl).hom
              (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) h) =
          (d f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).hom ≫
            Functor.whiskerLeft (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)
              (d g h (g ≫ h) rfl).hom) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        (d f (𝟙 Y) f (Category.comp_id f).symm).hom ≫
            Functor.whiskerLeft (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)
              (e Y).hom = 𝟙 (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        (d (𝟙 X) f f (Category.id_comp f).symm).hom ≫
            Functor.whiskerRight (e X).hom
              (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f) =
          𝟙 (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)) := by
  sorry

end AlgebraicGeometry.Etale
