/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import Mathlib.CategoryTheory.EssentialImage
/-!
# Exceptional adjunction on the comparison class

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-existence,
thm-sf-ambient-adjoint-class.md (blueprint: thm-sf-ambient-adjoint-class).

The interface retains the natural Hom equivalences and the compactification comparisons.
The right functor is written as the specified comparison composite, without an ambient
pro-etale adjunction hypothesis. A single etale right adjoint normalizes the right functors
for all compactifications; compatibility of the Hom equivalences characterizes the left
comparisons, and the right comparisons are identities in this normalization. The left
comparisons are required to equal the existing canonical comparison on every
bounded-below étale representative, rather than being chosen as a free coherent family.
-/

@[expose] public noncomputable section

set_option autoImplicit false

section HomDescent

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} B]
  (U : C ⥤ D) [U.IsEquivalence] (F : D ⥤ E) (I : D ⥤ B) (R : E ⥤ B)
  (Q : ObjectProperty E)
  (e : ∀ (X : C) (Y : E), Q Y → ((F.obj (U.obj X) ⟶ Y) ≃ (I.obj (U.obj X) ⟶ R.obj Y)))

variable
  (el : ∀ (X X' : C) (Y : E) (hY : Q Y) (a : X ⟶ X')
    (b : F.obj (U.obj X') ⟶ Y),
    e X Y hY (F.map (U.map a) ≫ b) = I.map (U.map a) ≫ e X' Y hY b)
  (er : ∀ (X : C) (Y Y' : E) (hY : Q Y) (hY' : Q Y')
    (a : F.obj (U.obj X) ⟶ Y) (b : Y ⟶ Y'),
    e X Y' hY' (a ≫ b) = e X Y hY a ≫ R.map b)

end CategoryTheory

end HomDescent

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The named direct-image comparison on D+, placed in the ordinary derived
categories using their specified inclusion comparisons. It is the actual counit mate.
Source: blueprint comparison-class adjunction, proper direct-image comparison
(blueprint: thm-sf-ambient-adjoint-class). -/
def fixedDirectImageComparisonIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V : Scheme.{u}} (c : S ⟶ V) [QuasiCompact c] [QuasiSeparated c] :
    DerivedCategory.Plus.ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlusCompatibility.symm _ ≪≫
    Functor.isoWhiskerLeft
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus
      (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight
      (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A c)
        (isIso_fixedComparisonDirectImageMatePlus A c)) DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategoryPlus
      (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategoryPlusCompatibility _

/-- Compact support comparison with the specified direct-image counit mate.
Source: blueprint comparison-class adjunction, chosen compactification
(blueprint: thm-sf-ambient-adjoint-class). -/
noncomputable def fixedCompactSupportComparisonIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (A : Type (u + 1)) [CommRing A] [Finite A] (c : Compactification f) :
    DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} A]) ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      DerivedCategory.Plus.ι ⋙ Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1}
        A) c ⋙
        D(ν^*(Y)[ModuleCat.{u + 1} A]) :=
  have := c.isProper
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
            Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) c.i).symm ≪≫
            Functor.mapDerivedCategoryCompIso _ _) R(ProEtale.lowerStar (ModuleCat.{u + 1} A) c.g)
              ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
        c.i).mapDerivedCategoryPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
      (fixedDirectImageComparisonIso A c.g).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
        c.i).mapDerivedCategoryPlusCompatibility _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι (Functor.associator _ _ _).symm

/-- Canonical compactification comparison on etale representatives, obtained by
transporting the canonical etale comparison through the specified compact-support maps.
Source: blueprint comparison-class adjunction, clause (3)
(blueprint: thm-sf-ambient-adjoint-class). -/
def fixedCompactSupportOriginIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :=
  fixedCompactSupportComparisonIso A c ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≪≫
    (fixedCompactSupportComparisonIso A d).symm

/-- The relative adjunction and its coherent compactification comparisons, with the right
functor normalized to `nu_X^* G Rnu_Y,*`. `P` and `Q` specify precisely the allowed inputs
and targets. For the finite coefficient ring `Λ`, the comparison components must equal
`fixedCompactSupportOriginIso`, the existing transport of the
canonical étale comparisons. The Hom bijection at `c₀` must be the transport of `adj` by
the fixed compact-support comparison and derived comparison adjunction. The datum also
includes preservation of bounded-below complexes by the transported right functor.
Source: Weil blueprint, thm-sf-ambient-adjoint-class.md, clauses (2)--(3)
(blueprint: thm-sf-ambient-adjoint-class). -/
structure FixedComparisonClassAdjunction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (P : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))
    (Q : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))) where
  /-- The transported ordinary right adjoint preserves bounded-below complexes. -/
  boundedBelow (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    _root_.DerivedCategory.TStructure.t.plus
      ((R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙
        D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L)
  /-- The adjunction bijections for each compactification and each allowed pair. -/
  homEquiv (c : Compactification f) (K) (hK : P K) (L) (hL : Q L) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K ⟶ L) ≃
      (K ⟶ (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L)
  /-- At the chosen compactification, the Hom bijection is the transported chosen
  étale adjunction, through the fixed compact-support and site comparisons. -/
  homEquiv_normalized
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : P (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj)) (L) (hL : Q L)
      (a : (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c₀).obj K.obj ⟶
        R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L) :
    homEquiv c₀ (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj) hK L hL
        ((fixedCompactSupportComparisonIso
            Λ c₀).hom.app K ≫
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm a) =
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).map ((adj.homEquiv K.obj _) a)
  /-- Naturality with respect to every morphism between allowed inputs. -/
  naturality_left (c : Compactification f) (K K') (hK : P K) (hK' : P K')
      (L) (hL : Q L) (a : K ⟶ K')
      (b : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K' ⟶ L) :
    homEquiv c K hK L hL
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map a ≫ b) =
      a ≫ homEquiv c K' hK' L hL b
  /-- Naturality with respect to every morphism between allowed targets. -/
  naturality_right (c : Compactification f) (K) (hK : P K)
      (L L') (hL : Q L) (hL' : Q L')
      (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K ⟶ L)
      (b : L ⟶ L') :
    homEquiv c K hK L' hL' (a ≫ b) =
      homEquiv c K hK L hL a ≫
        (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).map b
  /-- Compactification comparisons on exactly the permitted input class. -/
  comparison (c d : Compactification f) :
    P.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
      P.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d
  /-- On every étale-origin input, the comparison is the canonical étale comparison
  transported through `ν^*`; this fixes the comparison rather than allowing scalar twists. -/
  comparison_normalized (c d : Compactification f)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : P (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj)) :
    (comparison c d).hom.app ⟨D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj, hK⟩ =
      (fixedCompactSupportOriginIso Λ c d).hom.app K
  /-- Comparing a compactification with itself gives the identity. -/
  comparison_refl (c : Compactification f) : comparison c c = Iso.refl _
  /-- The comparison isomorphisms satisfy the cocycle condition. -/
  comparison_trans (c d e : Compactification f) :
    comparison c e = comparison c d ≪≫ comparison d e
  /-- The comparisons identify the Hom bijections; this determines their components. -/
  comparison_homEquiv (c d : Compactification f) (K) (hK : P K) (L) (hL : Q L)
      (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d).obj K ⟶ L) :
    homEquiv c K hK L hL ((comparison c d).hom.app ⟨K, hK⟩ ≫ a) =
      homEquiv d K hK L hL a

private abbrev comparisonOriginLift (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory :=
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).lift
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]))
    (fun K ↦ DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property)

private local instance comparisonOriginLift_full (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) : (comparisonOriginLift Λ X).Full where
  map_surjective {K L} a := by
    obtain ⟨b, hb⟩ :=
      (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).2 a.hom
    exact ⟨ObjectProperty.homMk b, by ext; exact hb⟩

private local instance comparisonOriginLift_faithful (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) : (comparisonOriginLift Λ X).Faithful where
  map_injective {K L} a b h := by
    ext
    exact (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).1
      (congrArg (fun t ↦ t.hom) h)

private local instance comparisonOriginLift_essSurj (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) : (comparisonOriginLift Λ X).EssSurj where
  mem_essImage K := by
    obtain ⟨K₀, hK₀, ⟨e⟩⟩ := K.property
    exact ⟨⟨K₀, hK₀⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

private local instance comparisonOriginLift_isEquivalence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    (comparisonOriginLift Λ X).IsEquivalence where

private def originComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d :=
  ((Functor.whiskeringLeft _ _ _).obj (comparisonOriginLift Λ X)).preimageIso
    (fixedCompactSupportOriginIso Λ c d)

end AlgebraicGeometry.ProEtale
