/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.IntegralAmbientCoefficientPresentation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Normalized integral and finite direct-image encodings

Source: Bhatt--Scholze, Section 6.5; Stacks 0D6E
(blueprint: def-sfb-integral-ambient-direct-image-encoding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u a av b bv c cv d dv w x y z
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme.IntegralAmbientTower
attribute [-instance] ConstantScalarRestriction.fixedAbelian
attribute [-instance] ConstantScalarRestriction.fixedPreadditive
attribute [-instance] ConstantScalarRestriction.fixedZeroMorphisms

attribute [instance] finiteFixed_additive finiteFixed_preservesFiniteLimits
attribute [instance] finiteFixed_preservesFiniteColimits

/-- A mixed-universe exact coefficient square, normalized on every complex by the
universal derived units. Source: Stacks 0D6E
(blueprint: def-sfb-integral-ambient-direct-image-encoding). -/
structure NormalizedSquare
    {A : Type a} [Category.{av} A] [Abelian A] [derA : HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type b} [Category.{bv} B] [Abelian B] [derB : HasDerivedCategory.{x} B]
    {C : Type c} [Category.{cv} C] [Abelian C] [derC : HasDerivedCategory.{y} C]
    [Abelian.HasKInjectiveResolutions C]
    {D : Type d} [Category.{dv} D] [Abelian D] [derD : HasDerivedCategory.{z} D]
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    [addF : F.Additive] [addG : G.Additive] [addU : U.Additive] [addV : V.Additive]
    [limU : PreservesFiniteLimits U] [colimU : PreservesFiniteColimits U]
    [limV : PreservesFiniteLimits V] [colimV : PreservesFiniteColimits V]
    (P : (F ⋙ V ⟶ U ⋙ G) → Prop) where
  ordinary : F ⋙ V ≅ U ⋙ G
  ordinary_property : P ordinary.hom
  derived : F.rightDerivedFunctor ⋙ V.mapDerivedCategory ≅
    U.mapDerivedCategory ⋙ G.rightDerivedFunctor
  normalization : ∀ J : CochainComplex A ℤ,
    V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ J) ≫
        derived.hom.app (DerivedCategory.Q.obj J) ≫
        G.rightDerivedFunctor.map (U.mapDerivedCategoryFactors.hom.app J) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app J) ≫
        G.rightDerivedFunctorUnitQ ((U.mapHomologicalComplex (.up ℤ)).obj J)

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)

/-- The normalized finite direct-image encoding retains the original scalar action.
The ordinary comparison is identity on sections; the derived comparison intertwines
its actual total right-derived units, on every complex, not just on its cohomology.
Source: Stacks 0D6E (blueprint: def-sfb-integral-ambient-direct-image-encoding). -/
def FiniteCoefficientPushEncoding {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  NormalizedSquare
      (C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1}
        (A ⧸ d.ideal ^ (n + 1))))
      (D := Sheaf (ProEt.topology Y) (ModuleCat.{u + 1}
        (A ⧸ d.ideal ^ (n + 1))))
      (derC := HasDerivedCategory.ofHasKInjectiveResolutions.{u + 1, u + 1, u + 2}
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1}
          (A ⧸ d.ideal ^ (n + 1)))))
      (derD := HasDerivedCategory.ofHasKInjectiveResolutions.{u + 1, u + 1, u + 2}
        (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1}
          (A ⧸ d.ideal ^ (n + 1)))))
      (addU := finiteFixed_additive X _) (addV := finiteFixed_additive Y _)
      (limU := finiteFixed_preservesFiniteLimits X _)
      (colimU := finiteFixed_preservesFiniteColimits X _)
      (limV := finiteFixed_preservesFiniteLimits Y _)
      (colimV := finiteFixed_preservesFiniteColimits Y _)
      (proEtaleRingModuleDirectImage f (d.finiteRing Y n)
        (d.finiteRing X n)
        (d.finiteRingIso f n))
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (A ⧸
          d.ideal ^ (n + 1))) f)
      (finiteFixed X (A ⧸ d.ideal ^ (n + 1)))
      (finiteFixed Y (A ⧸ d.ideal ^ (n + 1)))
    (fun η ↦ ∀ (M : reductionModules X (d.finiteRing X n))
      (V : Y.ProEtᵒᵖ)
      (s : (((finiteFixed Y (A ⧸
        d.ideal ^ (n + 1))).obj
        ((proEtaleRingModuleDirectImage f (d.finiteRing Y n)
          (d.finiteRing X n)
          (d.finiteRingIso f n)).obj M)).obj.obj V)),
    HEq ((η.app M).hom.app V s) s)

/-- The normalized finite square in the published derived-category coordinates.
Source: Stacks 0D6E (blueprint: def-sfb-integral-ambient-direct-image-encoding). -/
def FiniteCoefficientPushEncoding.comparison {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {n : ℕ}
    (H : FiniteCoefficientPushEncoding d f n) :
    d.finitePush f n ⋙
      finiteDerivedFixed Y (A ⧸ d.ideal ^ (n + 1)) ≅
    finiteDerivedFixed X (A ⧸ d.ideal ^ (n + 1)) ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1}
        (A ⧸ d.ideal ^ (n + 1))) f).rightDerivedFunctor :=
  NormalizedSquare.derived
    (addU := finiteFixed_additive X _) (addV := finiteFixed_additive Y _)
    (limU := finiteFixed_preservesFiniteLimits X _)
    (colimU := finiteFixed_preservesFiniteColimits X _)
    (limV := finiteFixed_preservesFiniteLimits Y _)
    (colimV := finiteFixed_preservesFiniteColimits Y _) H

/-- Specialize the same normalized finite square to the actual valuation-ring datum.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-direct-image-encoding). -/
abbrev FinitePushEncoding {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  FiniteCoefficientPushEncoding (datum.{u} l E π hπ) f n

/-- The specialization retains the exact normalized comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-direct-image-encoding). -/
abbrev FinitePushEncoding.comparison {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {n : ℕ}
    (H : FinitePushEncoding l E (π := π) (hπ := hπ) f n) :=
  FiniteCoefficientPushEncoding.comparison (datum.{u} l E π hπ) H

/-- The two encodings of the ordinary ambient direct image agree on sections and
on the universal right-derived units. This prevents replacing its induced action
by an unrelated action on an isomorphic abelian complex.
Source: Stacks 00YV and 0D6E (blueprint: def-sfb-integral-ambient-direct-image-encoding). -/
def AmbientEncoding {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (CX : CoefficientModel l E π hπ X) (CY : CoefficientModel l E π hπ Y) :=
  NormalizedSquare
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f)
      (proEtaleRingModuleDirectImage f
        ((datum.{u} l E π hπ).completedRing Y) ((datum.{u} l E π hπ).completedRing X)
        ((datum.{u} l E π hπ).integralRingIso f))
      (CX.modules.{u} l E).functor (CY.modules.{u} l E).functor
    (fun η ↦ ∀ (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) X))
      (V : Y.ProEtᵒᵖ)
      (s : (((CY.modules.{u} l E).functor.obj
        ((CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f).obj M)).val.obj V)),
    HEq ((η.app M).val.app V s) s)

end AlgebraicGeometry.Scheme.IntegralAmbientTower
