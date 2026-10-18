/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.Paper.AffineLineOrdinaryInvariance
import Sheaf.Paper.SupportedCupFunctoriality

/-!
# Affine-line invariance with closed supports

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence.proof.md, shear paragraph; Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy).

The pullbacks below are normalized by their ordinary section maps, then derived by
right-derived base change. Coefficients are the existing signed finite Tate sheaf on
Spec k, transported by exact inverse image. This realizes A(r) on every k-scheme
without choosing a root of unity or a trivialization. All supports are closed subschemes;
no finiteness condition is imposed on their ambient schemes.

## Main definitions and statement

* `affineSupportEtaleH` and `affineSupportProEtaleH`: the recorded supported cohomology.
* `affineSupportBaseChangeEtale` and `affineSupportBaseChangeProEtale`: projection pullback.
* `affineSupportSectionEtale` and `affineSupportSectionProEtale`: section pullback.
* `affineSupportComparison`: the canonical comparison of the two sites.
* `supportedAffineLineHomotopy`: invertibility, the comparison square, and all section
  identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Etale

/-- The module-valued specialization of the recorded support kernel.
Source: def-pur-support-cohomology, kernel formula
(blueprint: lem-pur-supported-affine-line-homotopy). -/
abbrev affineSupportKernel (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor X.smallEtaleTopology (ModuleCat.{u + 1} A)
    (supportRestrictionArrow i)

/-- Inclusion of the support kernel into sections on the terminal etale object.
Source: def-pur-support-cohomology, kernel formula
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportInclusion (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  kernel.ι (F.obj.map (supportRestrictionArrow i).op)

/-- The adjunction-unit map on sections, using the base change of the terminal object.
Source: blueprint shear paragraph, canonical pullback
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineGlobalSectionMap (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) ≫
    ((upperStar (ModuleCat.{u + 1} A) f).obj F).obj.map
      (show Scheme.Etale.mk (𝟙 Y) ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 X)) from
        MorphismProperty.Over.homMk (inv (pullback.snd (𝟙 X) f))
          (by change inv (pullback.snd (𝟙 X) f) ≫ pullback.snd (𝟙 X) f = 𝟙 Y; simp)).op

/-- Ordinary supported pullback is fixed uniquely by ordinary section pullback.
Source: Stacks Tag 09XP, functoriality of the support kernel; blueprint shear paragraph
(blueprint: lem-pur-supported-affine-line-homotopy).
Proof: a section vanishing off C pulls back to one vanishing off f inverse C.
The displayed complement equality identifies that open with the complement of D.
Factor the ordinary section map through the kernel. Its monic inclusion gives
uniqueness and naturality in the coefficient sheaf. -/
theorem affineSupportUnit_existsUnique (A : Type (u + 1)) [CommRing A]
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement) :
    ∃! α : affineSupportKernel A i ⟶
        upperStar (ModuleCat.{u + 1} A) f ⋙ affineSupportKernel A j,
      ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        α.app F ≫ affineSupportInclusion A j
            ((upperStar (ModuleCat.{u + 1} A) f).obj F) =
          affineSupportInclusion A i F ≫
            affineGlobalSectionMap A f F := by
  sorry

/-- The support kernel's canonical inverse-image unit, with its unique normalization.
Source: Stacks Tag 09XP, blueprint shear paragraph
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportUnit (A : Type (u + 1)) [CommRing A]
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement) :=
  (affineSupportUnit_existsUnique A i j f h).choose

/-- Canonical derived supported pullback, using the right-derived universal property.
Source: Stacks Tag 09XP, blueprint shear paragraph
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportDerivedMap (A : Type (u + 1)) [CommRing A]
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement) :
    (affineSupportKernel A i).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (affineSupportKernel A j).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ affineSupportUnit A i j f h)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Inclusion of the recorded support kernel into sections on the terminal object.
Source: def-pur-support-cohomology, kernel formula
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportInclusion (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  kernel.ι (F.obj.map (supportRestrictionArrow i).op)

/-- The pro-etale adjunction unit on sections over the terminal object.
Source: blueprint shear paragraph, canonical pullback
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineGlobalSectionMap (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app F).hom.app
      (op (Scheme.ProEt.mk (𝟙 X))) ≫
    ((upperStar (ModuleCat.{u + 1} A) f).obj F).obj.map
      (show Scheme.ProEt.mk (𝟙 Y) ⟶
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (Scheme.ProEt.mk (𝟙 X)) from
        MorphismProperty.Over.homMk (inv (pullback.snd (𝟙 X) f))
          (by change inv (pullback.snd (𝟙 X) f) ≫ pullback.snd (𝟙 X) f = 𝟙 Y; simp)).op

/-- Supported pro-etale pullback is uniquely determined by its ordinary section map.
Source: Stacks Tag 09XP, blueprint shear paragraph
(blueprint: lem-pur-supported-affine-line-homotopy).
Proof: pullback of a section zero on the complement is zero on its inverse image.
The complement equation identifies this open with the target complement. Factor
through the support kernel; its monic inclusion proves uniqueness and naturality. -/
theorem affineSupportUnit_existsUnique (A : Type (u + 1)) [CommRing A]
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement) :
    ∃! α : supportSections i A ⟶
        upperStar (ModuleCat.{u + 1} A) f ⋙ supportSections j A,
      ∀ F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A),
        α.app F ≫ affineSupportInclusion A j
            ((upperStar (ModuleCat.{u + 1} A) f).obj F) =
          affineSupportInclusion A i F ≫ affineGlobalSectionMap A f F := by
  sorry

/-- Canonical supported pro-etale section pullback with its kernel normalization.
Source: Stacks Tag 09XP, blueprint shear paragraph
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportUnit (A : Type (u + 1)) [CommRing A]
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement) :=
  (affineSupportUnit_existsUnique A i j f h).choose

/-- Canonical derived pro-etale supported pullback, from the normalized kernel map.
Source: Stacks Tag 09XP, blueprint shear paragraph
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportDerivedMap (A : Type (u + 1)) [CommRing A]
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement) :
    (supportSections i A).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (supportSections j A).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ affineSupportUnit A i j f h)

/-- The evaluation-kernel model of the canonical site-comparison unit.
Source: Stacks Tags 099V and 09XP, blueprint comparison clause
(blueprint: lem-pur-supported-affine-line-homotopy).
Proof: the comparison adjunction unit has the same sections on an etale object.
Its naturality for the open-complement arrow gives a map between the two support
kernels. The monic kernel inclusion gives uniqueness and naturality in F. This is
exactly the ordinary comparison unit, expressed in the terminal-evaluation model. -/
theorem affineSupportSiteUnit_existsUnique (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! α : Etale.affineSupportKernel A i ⟶
        comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙ supportSections i A,
      ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        α.app F ≫ affineSupportInclusion A i
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F) =
          Etale.affineSupportInclusion A i F ≫
            ((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.app
              (op (Scheme.Etale.mk (𝟙 X))) := by
  sorry

/-- The canonical unit on support kernels, fixed by its ordinary adjunction unit.
Source: Stacks Tags 099V and 09XP, blueprint comparison clause
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportSiteUnit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  (affineSupportSiteUnit_existsUnique A i).choose

/-- The canonical comparison of supported derived sections in the evaluation model.
Source: Stacks Tags 099V and 09XP, blueprint comparison clause
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportSiteDerivedMap (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    (Etale.affineSupportKernel A i).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus ⋙
        (supportSections i A).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ affineSupportSiteUnit A i)

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The existing finite Tate sheaf over the fixed geometric base, for every integer r.
The ring characteristic is a canonical annihilator, so no divisibility of n is assumed.
Source: purity conventions; Stacks Tag 03PK
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportBaseTwist (P : PurityFiniteSetting.{u}) (r : ℤ) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient)
    (Spec (.of P.field.k)) (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r

/-- Canonical coefficient transport of A(r) to an arbitrary k-scheme.
Source: purity conventions; Stacks Tag 03PK
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportEtaleTwist (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (r : ℤ) :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).obj (P.affineSupportBaseTwist r)

/-- The etale-origin pro-etale coefficient transport, using the existing comparison.
Source: purity conventions, site comparison clause
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportProEtaleTwist (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (r : ℤ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
    (P.affineSupportEtaleTwist a r)

/-- The module-valued kernel model of the stated supported etale cohomology.
It is the existing supported-section functor, derived and evaluated on A(r)[0].
Forgetting scalars gives the abelian supported cohomology of the conventions.
Source: def-pur-support-cohomology and Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportEtaleH (P : PurityFiniteSetting.{u}) {C X : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (a : X ⟶ Spec (.of P.field.k)) (q r : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) q).obj
    ((Etale.affineSupportKernel P.Coefficient i).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.affineSupportEtaleTwist a r)))

/-- The recorded pro-etale support hypercohomology, on the etale-origin twist A(r)[0].
Source: def-pur-support-cohomology and Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportProEtaleH (P : PurityFiniteSetting.{u}) {C X : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (a : X ⟶ Spec (.of P.field.k)) (q r : ℤ) :=
  ProEtale.supportHypercohomology i P.Coefficient q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.affineSupportProEtaleTwist a r))

/-- The actual etale cohomological pullback, with composition transport of the base twist.
Source: blueprint shear paragraph and Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportEtalePullback (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement)
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (ha : aY = f ≫ aX) (q r : ℤ) :
    P.affineSupportEtaleH i aX q r ⟶ P.affineSupportEtaleH j aY q r :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) q).map
    ((Etale.affineSupportDerivedMap P.Coefficient i j f h).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.affineSupportEtaleTwist aX r)) ≫
      (Etale.affineSupportKernel P.Coefficient j).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f) 0).hom.app
            (P.affineSupportEtaleTwist aX r) ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f aX aY ha).inv.app
              (P.affineSupportBaseTwist r))))

/-- The actual pro-etale cohomological pullback. Its coefficient map is the canonical
comparison/pullback mate followed by the same etale composition transport.
Source: blueprint shear paragraph and Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportProEtalePullback (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (f : Y ⟶ X)
    (h : f ⁻¹ᵁ i.openComplement = j.openComplement)
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (ha : aY = f ≫ aX) (q r : ℤ) :
    P.affineSupportProEtaleH i aX q r ⟶ P.affineSupportProEtaleH j aY q r :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) q).map
    ((ProEtale.affineSupportDerivedMap P.Coefficient i j f h).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.affineSupportProEtaleTwist aX r)) ≫
      (ProEtale.supportSections j P.Coefficient).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f) 0).hom.app
            (P.affineSupportProEtaleTwist aX r) ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((ProEtale.supportSiteComparisonCoefficientPullbackIso
                (ModuleCat.{u + 1} P.Coefficient) f).inv.app (P.affineSupportEtaleTwist aX r) ≫
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map
                ((Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f aX aY ha).inv.app
                  (P.affineSupportBaseTwist r)))))

/-- The canonical comparison on integer-degree supported cohomology, including
transport of the coefficient sheaf in degree zero.
Source: blueprint comparison clause, Stacks Tags 099V and 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportComparison (P : PurityFiniteSetting.{u}) {C X : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (a : X ⟶ Spec (.of P.field.k)) (q r : ℤ) :
    P.affineSupportEtaleH i a q r ⟶ P.affineSupportProEtaleH i a q r :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) q).map
    ((ProEtale.affineSupportSiteDerivedMap P.Coefficient i).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.affineSupportEtaleTwist a r)) ≫
      (ProEtale.supportSections i P.Coefficient).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusSingleFunctor
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X) 0).hom.app
            (P.affineSupportEtaleTwist a r)))

/-- The complement of the inverse-image closed subscheme is the inverse-image open.
Source: Stacks Tag 09XP, pair functoriality; blueprint definition of C_1
(blueprint: lem-pur-supported-affine-line-homotopy).
Proof: the base change of a closed immersion identifies its image with the inverse
image of the original closed image. Taking complements gives the open equality. -/
theorem affineSupportProjectionComplement {C X Y : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    f ⁻¹ᵁ i.openComplement = (pullback.snd i f).openComplement := by
  sorry

/-- Every section recovers precisely the original support, scheme-theoretically.
Source: blueprint shear paragraph, section clause; Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy).
Proof: inverse images compose. The inverse image along s of f inverse C is the
inverse image along s followed by f of C, hence C by the section equation. Apply
this equality to the open complements; no regularity or smoothness is used. -/
theorem affineSupportSectionComplement {C X Y : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ f = 𝟙 X) :
    s ⁻¹ᵁ (pullback.snd i f).openComplement = i.openComplement := by
  sorry

/-- Pullback to the inverse-image closed subscheme, with canonical base coefficients.
Source: blueprint shear paragraph, definition of C_1; Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportBaseChangeEtale (P : PurityFiniteSetting.{u})
    {C X Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (a : X ⟶ Spec (.of P.field.k)) (f : Y ⟶ X) (q r : ℤ) :=
  P.affineSupportEtalePullback i (pullback.snd i f) f
    (affineSupportProjectionComplement i f) a (f ≫ a) rfl q r

/-- Canonical section pullback with the original support C, using s inverse f inverse C = C.
Source: blueprint shear paragraph, section clause; Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportSectionEtale (P : PurityFiniteSetting.{u})
    {C X Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (a : X ⟶ Spec (.of P.field.k)) (f : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ f = 𝟙 X) (q r : ℤ) :=
  P.affineSupportEtalePullback (pullback.snd i f) i s
    (affineSupportSectionComplement i f s hs) (f ≫ a) a
    (by rw [← Category.assoc, hs, Category.id_comp]) q r

/-- Pullback to the inverse-image closed subscheme, with canonical base coefficients.
Source: blueprint shear paragraph, definition of C_1; Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportBaseChangeProEtale (P : PurityFiniteSetting.{u})
    {C X Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (a : X ⟶ Spec (.of P.field.k)) (f : Y ⟶ X) (q r : ℤ) :=
  P.affineSupportProEtalePullback i (pullback.snd i f) f
    (affineSupportProjectionComplement i f) a (f ≫ a) rfl q r

/-- Canonical section pullback with the original support C, using s inverse f inverse C = C.
Source: blueprint shear paragraph, section clause; Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy). -/
def affineSupportSectionProEtale (P : PurityFiniteSetting.{u})
    {C X Y : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (a : X ⟶ Spec (.of P.field.k)) (f : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ f = 𝟙 X) (q r : ℤ) :=
  P.affineSupportProEtalePullback (pullback.snd i f) i s
    (affineSupportSectionComplement i f s hs) (f ≫ a) a
    (by rw [← Category.assoc, hs, Category.id_comp]) q r

/-- Affine-line projection pullback is invertible with arbitrary closed supports,
on both small sites, compatibly with canonical comparison. Every section gives its
inverse; in particular the zero and unit sections give equal maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence.proof.md, shear paragraph; Stacks Tag 09XP
(blueprint: lem-pur-supported-affine-line-homotopy).

Proof:
1. Set U = X minus C. The complement of C_1 is A1_U. Apply
lem-pur-affine-line-ordinary-invariance to X and U with the fixed A(r), for arbitrary
positive coefficient level n. This gives ordinary projection isomorphisms in every
integer degree on both small sites, including the negative degrees of a sheaf.
2. Use thm-pur-with-support-exactness for the two pairs. The canonical pullbacks
commute with restriction and localization boundaries by
lem-pur-supported-cup-functoriality. Hence they form a diagram of localization sequences.
3. In the five-term segment H^(q-1)(X) to H^(q-1)(U) to H^q_C(X) to H^q(X) to H^q(U),
the four outside vertical maps are isomorphisms. To prove injectivity of the middle
map, an element in its kernel first maps to zero in H^q(X), so is a boundary of an
element in H^(q-1)(U). The latter maps to an element coming from H^(q-1)(A1_X);
lift it using the first outside isomorphism and cancel using the second. Its
boundary is zero. For surjectivity, lift the image of a target supported class in
H^q(A1_X) to H^q(X). Its restriction to U is zero by injectivity of the last outside
map, so lift it to H^q_C(X). The difference from the desired target is a boundary
from H^(q-1)(A1_U); lift that boundary using the second outside isomorphism and add it.
4. The comparison clause of lem-pur-supported-cup-functoriality identifies the
supported pullbacks and boundary maps on the two sites, so the projection pullbacks
form the displayed commuting square with the canonical comparison maps (which the
node does not assert to be invertible). Our maps are exactly these maps:
their ordinary units are fixed by kernel inclusions, and the derived maps are
fixed by the right-derived universal property, not by a choice of isomorphism.
5. For any section s, s followed by p is the identity. Identity and composition
functoriality give s* p* = id with inverse-image support C. Invertibility of p*
gives also p* s* = id. Thus s* is its inverse, for every section. The zero and unit
sections are two such sections and therefore give the same inverse. This argument
uses no finite-type, separatedness, smoothness, regularity, connectedness or strict
locality hypothesis on X or C. -/
theorem supportedAffineLineHomotopy (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (i : C ⟶ X) [IsClosedImmersion i] (q r : ℤ) :
    IsIso (P.affineSupportBaseChangeEtale i
      (X ↘ Spec (.of P.field.k))
      (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r) ∧
    IsIso (P.affineSupportBaseChangeProEtale i
      (X ↘ Spec (.of P.field.k))
      (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r) ∧
    (P.affineSupportBaseChangeEtale i
        (X ↘ Spec (.of P.field.k))
        (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r ≫
      P.affineSupportComparison
        (pullback.snd i (AffineSpace (ULift.{u} (Fin 1)) X ↘ X))
        ((AffineSpace (ULift.{u} (Fin 1)) X ↘ X) ≫
          (X ↘ Spec (.of P.field.k))) q r =
      P.affineSupportComparison i (X ↘ Spec (.of P.field.k)) q r ≫
        P.affineSupportBaseChangeProEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r) ∧
    (∀ (s : X ⟶ AffineSpace (ULift.{u} (Fin 1)) X)
        (hs : s ≫ (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) = 𝟙 X),
      (P.affineSupportBaseChangeEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r ≫
        P.affineSupportSectionEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) s hs q r = 𝟙 _) ∧
      (P.affineSupportSectionEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) s hs q r ≫
        P.affineSupportBaseChangeEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r = 𝟙 _) ∧
      (P.affineSupportBaseChangeProEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r ≫
        P.affineSupportSectionProEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) s hs q r = 𝟙 _) ∧
      (P.affineSupportSectionProEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) s hs q r ≫
        P.affineSupportBaseChangeProEtale i
          (X ↘ Spec (.of P.field.k))
          (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) q r = 𝟙 _)) ∧
    (P.affineSupportSectionEtale i
        (X ↘ Spec (.of P.field.k))
        (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X)
        (AffineSpace.zeroSection_comp_over _ _) q r =
      P.affineSupportSectionEtale i
        (X ↘ Spec (.of P.field.k))
        (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) X)
        (AffineSpace.oneSection_comp_over _ _) q r) ∧
    (P.affineSupportSectionProEtale i
        (X ↘ Spec (.of P.field.k))
        (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X)
        (AffineSpace.zeroSection_comp_over _ _) q r =
      P.affineSupportSectionProEtale i
        (X ↘ Spec (.of P.field.k))
        (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) X)
        (AffineSpace.oneSection_comp_over _ _) q r) := by
  sorry

end WeilConjectures.PurityFiniteSetting
