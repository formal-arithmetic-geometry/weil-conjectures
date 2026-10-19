/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

import Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Unbounded supported sections and etale/pro-etale direct image

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-kunneth-supported.proof.md, paragraph 4; Stacks Tags 099R, 070K, 08BJ and 08FI
(blueprint: lem-pur-derived-support-comparison-direct-image).

Fixed-ring module sheaves encode ordinary modules over the constant ring sheaf.
All derived functors below are unbounded. The comparison data are normalized by
literal restriction kernels and by the canonical derived-functor units.
-/

@[expose] public section

set_option autoImplicit false

universe u vC uC vD uD wC wD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.ProEtale

/-- The canonical map from the termwise functor to its total derived functor.
Source: Stacks Tag 070Y, resolution normalization
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportResolutionUnit
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    [HasKInjectiveResolutions C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  ((DerivedCategory.quotientCompQhIso D).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C _).obj I) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app I)

/-- The resolution-unit equation for a comparison of composite right derived functors.
Source: Stacks Tag 070Y (blueprint: lem-pur-derived-support-comparison-direct-image). -/
def supportCompositionNormalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H)
    (b : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (I : CochainComplex C ℤ) : Prop :=
  supportResolutionUnit G ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
    G.rightDerivedFunctor.map (supportResolutionUnit F I) ≫
      b.hom.app (DerivedCategory.Q.obj I) =
  DerivedCategory.Q.map ((e.hom.mapHomologicalComplex (.up ℤ)).app I) ≫
    supportResolutionUnit H I

/-- The compatibility equation for restriction and a comparison of composite functors.
Source: the restriction square in blueprint paragraph 4
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
def supportRestrictionSquare
    {C D B E U : Type*}
    [Category C] [Category D] [Category B] [Category E] [Category U]
    (F : C ⥤ D) (R : D ⥤ E) (S : C ⥤ B) (H : B ⥤ E)
    (K : D ⥤ U) (P : C ⥤ U) (K' : E ⥤ U) (P' : B ⥤ U)
    (b : F ⋙ K ⟶ P) (r : F ⋙ R ⟶ S ⋙ H) (b' : H ⋙ K' ⟶ P')
    (et : K ⟶ R ⋙ K') (pro : P ⟶ S ⋙ P') : Prop :=
  b ≫ pro = Functor.whiskerLeft F et ≫ Functor.whiskerRight r K' ≫
    Functor.whiskerLeft S b'

variable (A : Type (u + 1)) [CommRing A]

/-- The existing kernel-of-restriction functor with fixed scalar coefficients.
Source: blueprint paragraph 4 and the kernel formula of def-pur-support-cohomology
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  Sheaf.supportedSectionsFunctor (T.smallEtaleTopology) (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)

/-- Evaluation on the final scheme, the concrete global-sections model.
Source: Stacks Tag 099R, final-object comparison
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportEvalEt (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  sheafToPresheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))

/-- The kernel inclusion, namely forgetting supports.
Source: blueprint paragraph 4, support localization diagram
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportForgetEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : supportEt A i ⟶ supportEvalEt A T where
  app F := kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op)
  naturality f := by simp [supportEt, supportEvalEt, Sheaf.supportedSectionsFunctor]

/-- The existing kernel-of-restriction functor with fixed scalar coefficients.
Source: blueprint paragraph 4 and the kernel formula of def-pur-support-cohomology
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
    (supportRestrictionArrow i)

/-- Evaluation on the final scheme, the concrete global-sections model.
Source: Stacks Tag 099R, final-object comparison
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportEvalPro (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))

/-- The kernel inclusion, namely forgetting supports.
Source: blueprint paragraph 4, support localization diagram
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportForgetPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : supportPro A i ⟶ supportEvalPro A T where
  app F := kernel.ι (F.obj.map (supportRestrictionArrow i).op)
  naturality f := by simp [supportPro, supportEvalPro, Sheaf.supportedSectionsFunctor]

/-- The original-site direct image, restriction along the etale inclusion.
Source: Stacks Tag 099R (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportNu (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  comparisonLowerStar (ModuleCat.{u + 1} A) T

/-- The exact open restriction on etale module sheaves.
Source: Stacks Tag 08FI (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportRestrictEt {T : Scheme.{u}} (V : T.Opens) :=
  Etale.openImmersionRestriction (ModuleCat.{u + 1} A) V.ι

/-- The exact open restriction on pro-etale module sheaves.
Source: Stacks Tag 08FI (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportRestrictPro {T : Scheme.{u}} (V : T.Opens) :=
  openImmersionRestriction (ModuleCat.{u + 1} A) V.ι

/-- The existing right-image adjunction makes etale restriction a left adjoint.
Source: Stacks Tag 00XZ (blueprint: lem-pur-derived-support-comparison-direct-image). -/
instance supportRestrictEt_isLeftAdjoint {T : Scheme.{u}} (V : T.Opens) :
    (supportRestrictEt A V).IsLeftAdjoint :=
  (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) V.ι).isLeftAdjoint

/-- The existing right-image adjunction makes pro-etale restriction a left adjoint.
Source: Stacks Tag 00XZ (blueprint: lem-pur-derived-support-comparison-direct-image). -/
instance supportRestrictPro_isLeftAdjoint {T : Scheme.{u}} (V : T.Opens) :
    (supportRestrictPro A V).IsLeftAdjoint :=
  (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) V.ι).isLeftAdjoint

/-- The canonical adjunction on unbounded derived categories.
Source: Stacks Tag 09T5 (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportDerivedAdjunction (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⊣
      (supportNu A T).rightDerivedFunctor :=
  (comparisonAdjunction (ModuleCat.{u + 1} A) T).mapDerivedCategoryRightDerivedAdjunction

/-- Ordinary restriction of sections to the open subscheme, sectionwise.
Source: blueprint paragraph 4, restriction square
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportSectionRestrictionEt {T : Scheme.{u}} (V : T.Opens) :
    supportEvalEt A T ⟶ supportRestrictEt A V ⋙ supportEvalEt A V where
  app F := F.obj.map
    (MorphismProperty.Over.homMk V.ι (by change V.ι ≫ 𝟙 T = _; simp) :
      Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk (𝟙 T)).op
  naturality _ _ f := (f.hom.naturality _).symm

/-- Ordinary restriction of sections to the open subscheme, sectionwise.
Source: blueprint paragraph 4, restriction square
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportSectionRestrictionPro {T : Scheme.{u}} (V : T.Opens) :
    supportEvalPro A T ⟶ supportRestrictPro A V ⋙ supportEvalPro A V where
  app F := F.obj.map
    (MorphismProperty.Over.homMk V.ι (by change V.ι ≫ 𝟙 T = _; simp) :
      Scheme.ProEt.mk V.ι ⟶ Scheme.ProEt.mk (𝟙 T)).op
  naturality _ _ f := (f.hom.naturality _).symm

/-- The literal identity between the two underived support kernels.
Source: Stacks Tag 099R (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportKernelIdentity {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : supportNu A T ⋙ supportEt A i ≅ supportPro A i :=
  Iso.refl _

/-- The literal final-object direct-image identity.
Source: Stacks Tag 099R (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportEvaluationIdentity (T : Scheme.{u}) :
    supportNu A T ⋙ supportEvalEt A T ≅ supportEvalPro A T :=
  Iso.refl _

/-- The literal open-restriction/direct-image identity.
Source: Stacks Tags 099R and 08FI
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportOpenIdentity {T : Scheme.{u}} (V : T.Opens) :
    supportNu A T ⋙ supportRestrictEt A V ≅
      supportRestrictPro A V ⋙ supportNu A V :=
  Iso.refl _

/-- Open pullback comparison with the coefficient category kept abstract.
Source: Stacks Tag 00WX (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportCoefficientOpenPullback
    (D : Type vD) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {T : Scheme.{u}} (V : T.Opens) :
    Etale.openImmersionRestriction D V.ι ⋙ comparisonUpperStar D V ≅
      comparisonUpperStar D T ⋙ openImmersionRestriction D V.ι :=
  Functor.isoWhiskerRight (Etale.upperStarIsoOpenImmersionRestriction D V.ι).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso D V.ι ≪≫
      Functor.isoWhiskerLeft _ (upperStarIsoOpenImmersionRestriction D V.ι)

/-- Descent of the specified open comparison for an abstract coefficient category.
Source: Stacks Tag 015F (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportDerivedCoefficientOpenPullback
    (D : Type vD) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {T : Scheme.{u}} (V : T.Opens)
    [(Etale.openImmersionRestriction D V.ι).IsLeftAdjoint]
    [(openImmersionRestriction D V.ι).IsLeftAdjoint] :
    (Etale.openImmersionRestriction D V.ι).mapDerivedCategory ⋙
        (comparisonUpperStar D V).mapDerivedCategory ≅
      (comparisonUpperStar D T).mapDerivedCategory ⋙
        (openImmersionRestriction D V.ι).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (Etale.openImmersionRestriction D V.ι)
    (comparisonUpperStar D V)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (supportCoefficientOpenPullback D V) ≪≫
      Functor.mapDerivedCategoryCompIso (comparisonUpperStar D T)
        (openImmersionRestriction D V.ι)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical comparison-pullback isomorphism in open restriction form.
Source: lem-weil-pbc-comparison-pullback, its adjunction-mate normalization
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportOpenPullback {T : Scheme.{u}} (V : T.Opens) :
    supportRestrictEt A V ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) V ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportRestrictPro A V :=
  supportCoefficientOpenPullback (ModuleCat.{u + 1} A) V

/-- The same canonical inverse-image comparison on unbounded derived categories.
Source: lem-weil-pbc-comparison-pullback and Stacks Tag 015F
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportDerivedOpenPullback {T : Scheme.{u}} (V : T.Opens) :
    (supportRestrictEt A V).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        (supportRestrictPro A V).mapDerivedCategory :=
  supportDerivedCoefficientOpenPullback (ModuleCat.{u + 1} A) V

/-- Canonical supported direct-image comparison, including all its normalizations.
The fields provide conclusions, not extra hypotheses. Each auxiliary map is fixed
by its sectionwise or resolution-unit equation. Thus these are the canonical maps,
including on arbitrary unbounded complexes and arbitrary opens.
Source: blueprint paragraph 4; Stacks Tags 099R, 070Y, 08BJ and 08FI
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
structure DerivedSupportDirectImageComparison where
  /-- The natural isomorphism b for every closed immersion. -/
  b : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i],
    (supportNu A T).rightDerivedFunctor ⋙ (supportEt A i).rightDerivedFunctor ≅
      (supportPro A i).rightDerivedFunctor
  /-- The final-object comparison, on all complexes. -/
  g : ∀ T : Scheme.{u},
    (supportNu A T).rightDerivedFunctor ⋙ (supportEvalEt A T).rightDerivedFunctor ≅
      (supportEvalPro A T).rightDerivedFunctor
  /-- Identity on the indicated K-injective section complex. -/
  kernel_normalization : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    supportCompositionNormalization (supportNu A T) (supportEt A i) (supportPro A i)
      (supportKernelIdentity A i) (b i) J
  /-- Identity on the indicated K-injective section complex. -/
  final_normalization : ∀ (T : Scheme.{u})
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    supportCompositionNormalization (supportNu A T) (supportEvalEt A T) (supportEvalPro A T)
      (supportEvaluationIdentity A T) (g T) J
  /-- The square with the canonical inclusions that forget supports. -/
  forget : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i],
    (b i).hom ≫ Functor.rightDerivedFunctorNatTrans (supportForgetPro A i) =
      Functor.whiskerLeft (supportNu A T).rightDerivedFunctor
        (Functor.rightDerivedFunctorNatTrans (supportForgetEt A i)) ≫ (g T).hom
  /-- At full support forgetting is invertible; the previous square identifies b with g. -/
  full_support : ∀ T : Scheme.{u},
    IsIso (Functor.rightDerivedFunctorNatTrans (supportForgetEt A (𝟙 T))) ∧
      IsIso (Functor.rightDerivedFunctorNatTrans (supportForgetPro A (𝟙 T)))
  /-- Restriction on the ordinary supported kernels. -/
  openEt : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (V : T.Opens),
    supportEt A i ⟶ supportRestrictEt A V ⋙ supportEt A (pullback.snd i V.ι)
  /-- Restriction is precisely restriction of ordinary sections, factored through the kernel. -/
  openEt_sections : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
      (V : T.Opens),
    openEt i V ≫ Functor.whiskerLeft (supportRestrictEt A V)
        (supportForgetEt A (pullback.snd i V.ι)) =
      supportForgetEt A i ≫ supportSectionRestrictionEt A V
  /-- Restriction of the unbounded derived support functor. -/
  derivedOpenEt : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (V : T.Opens),
    (supportEt A i).rightDerivedFunctor ⟶
      (supportRestrictEt A V).mapDerivedCategory ⋙
        (supportEt A (pullback.snd i V.ι)).rightDerivedFunctor
  /-- The derived restriction is computed by the actual kernel restriction on K-injectives. -/
  derivedOpenEt_normalization : ∀ {C T : Scheme.{u}} (i : C ⟶ T)
      [IsClosedImmersion i] (V : T.Opens)
      (I : CochainComplex (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A)) ℤ)
      [I.IsKInjective],
    supportResolutionUnit (supportEt A i) I ≫
        (derivedOpenEt i V).app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
          (((openEt i V).mapHomologicalComplex (ComplexShape.up ℤ)).app I) ≫
        supportResolutionUnit (supportEt A (pullback.snd i V.ι))
          (((supportRestrictEt A V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (supportEt A (pullback.snd i V.ι)).rightDerivedFunctor.map
          ((supportRestrictEt A V).mapDerivedCategoryFactors.inv.app I)
  /-- Restriction on the ordinary supported kernels. -/
  openPro : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (V : T.Opens),
    supportPro A i ⟶ supportRestrictPro A V ⋙ supportPro A (pullback.snd i V.ι)
  /-- Restriction is precisely restriction of ordinary sections, factored through the kernel. -/
  openPro_sections : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
      (V : T.Opens),
    openPro i V ≫ Functor.whiskerLeft (supportRestrictPro A V)
        (supportForgetPro A (pullback.snd i V.ι)) =
      supportForgetPro A i ≫ supportSectionRestrictionPro A V
  /-- Restriction of the unbounded derived support functor. -/
  derivedOpenPro : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (V : T.Opens),
    (supportPro A i).rightDerivedFunctor ⟶
      (supportRestrictPro A V).mapDerivedCategory ⋙
        (supportPro A (pullback.snd i V.ι)).rightDerivedFunctor
  /-- The derived restriction is computed by the actual kernel restriction on K-injectives. -/
  derivedOpenPro_normalization : ∀ {C T : Scheme.{u}} (i : C ⟶ T)
      [IsClosedImmersion i] (V : T.Opens)
      (I : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [I.IsKInjective],
    supportResolutionUnit (supportPro A i) I ≫
        (derivedOpenPro i V).app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
          (((openPro i V).mapHomologicalComplex (ComplexShape.up ℤ)).app I) ≫
        supportResolutionUnit (supportPro A (pullback.snd i V.ι))
          (((supportRestrictPro A V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (supportPro A (pullback.snd i V.ι)).rightDerivedFunctor.map
          ((supportRestrictPro A V).mapDerivedCategoryFactors.inv.app I)
  /-- The derived open-restriction identification for direct image. -/
  rho : ∀ {T : Scheme.{u}} (V : T.Opens),
    (supportNu A T).rightDerivedFunctor ⋙ (supportRestrictEt A V).mapDerivedCategory ≅
      (supportRestrictPro A V).mapDerivedCategory ⋙ (supportNu A V).rightDerivedFunctor
  /-- This identification is induced by the sectionwise identity, on K-injectives. -/
  rho_normalization : ∀ {T : Scheme.{u}} (V : T.Opens)
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    (supportRestrictEt A V).mapDerivedCategory.map
        (supportResolutionUnit (supportNu A T) J) ≫
      (rho V).hom.app (DerivedCategory.Q.obj J) =
    (supportRestrictEt A V).mapDerivedCategoryFactors.hom.app
        (((supportNu A T).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
      DerivedCategory.Q.map
        (((supportOpenIdentity A V).hom.mapHomologicalComplex (ComplexShape.up ℤ)).app J) ≫
      supportResolutionUnit (supportNu A V)
        (((supportRestrictPro A V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
      (supportNu A V).rightDerivedFunctor.map
        ((supportRestrictPro A V).mapDerivedCategoryFactors.inv.app J)
  /-- The support comparison commutes with restriction to every open. -/
  open_square : ∀ {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] (V : T.Opens),
    supportRestrictionSquare (supportNu A T).rightDerivedFunctor
      (supportRestrictEt A V).mapDerivedCategory (supportRestrictPro A V).mapDerivedCategory
      (supportNu A V).rightDerivedFunctor (supportEt A i).rightDerivedFunctor
      (supportPro A i).rightDerivedFunctor
      (supportEt A (pullback.snd i V.ι)).rightDerivedFunctor
      (supportPro A (pullback.snd i V.ι)).rightDerivedFunctor
      (b i).hom (rho V).hom (b (pullback.snd i V.ι)).hom
      (derivedOpenEt i V) (derivedOpenPro i V)
  /-- The restriction identification also intertwines the canonical derived adjunction units. -/
  unit_square : ∀ {T : Scheme.{u}} (V : T.Opens)
      (M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
    (supportRestrictEt A V).mapDerivedCategory.map
        ((supportDerivedAdjunction A T).unit.app M) ≫
      (rho V).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M) ≫
      (supportNu A V).rightDerivedFunctor.map ((supportDerivedOpenPullback A V).inv.app M) =
    (supportDerivedAdjunction A V).unit.app
        ((supportRestrictEt A V).mapDerivedCategory.obj M)

private lemma worker_map_inv_hom_assoc
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (e : X ≅ Y) {Z : D} (f : F.obj Y ⟶ Z) :
    F.map e.inv ≫ F.map e.hom ≫ f = f := by
  rw [← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

private lemma worker_compUnit_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (X : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app X =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app X
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [Functor.rightDerivedFunctorCompUnit, hi]

private lemma worker_comp_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (X : HomotopyCategory C (.up ℤ)) :
    G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) ≫
        (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj X) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) ≫
      H.rightDerivedFunctorUnit.app X := by
  have hf : (F ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh
      (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  have hf' : Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit := by
    rw [← hf, Category.assoc, ← Functor.whiskerLeft_comp]
    simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom,
      Iso.hom_inv_id_assoc]
    exact Functor.rightDerivedNatTrans_fac _ _ _ _ (HomotopyCategory.quasiIso C (.up ℤ)) _
  have hx := congr_app hf' X
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    worker_compUnit_app, Category.assoc] using hx

set_option backward.isDefEq.respectTransparency false in
private lemma worker_comp_nat
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G H : D ⥤ E) (U V : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [U.Additive] [V.Additive]
    [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ U) (f : F ⋙ H ≅ V) (τ : G ⟶ H) (σ : U ⟶ V)
    (h : e.hom ≫ σ = Functor.whiskerLeft F τ ≫ f.hom) :
    (Functor.rightDerivedFunctorCompIso' F G e).hom ≫
        Functor.rightDerivedFunctorNatTrans σ =
      Functor.whiskerLeft F.rightDerivedFunctor
          (Functor.rightDerivedFunctorNatTrans τ) ≫
        (Functor.rightDerivedFunctorCompIso' F H f).hom := by
  apply (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).rightDerived_ext
    (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (.up ℤ))
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, worker_compUnit_app,
    Category.assoc]
  have hu (T S : C ⥤ E) [T.Additive] [S.Additive] (a : T ⟶ S) :
      T.rightDerivedFunctorUnit.app X ≫
        (Functor.rightDerivedFunctorNatTrans a).app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a (.up ℤ)).app X) ≫
        S.rightDerivedFunctorUnit.app X := by
    simp [Functor.rightDerivedFunctorNatTrans]
  have ht := (Functor.rightDerivedFunctorNatTrans τ).naturality
    (F.rightDerivedFunctorUnit.app X)
  erw [reassoc_of% (worker_comp_fac F G U e X), hu, reassoc_of% ht]
  have ht' : G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
      (Functor.rightDerivedFunctorNatTrans τ).app
        (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      H.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) := by
    simp [Functor.rightDerivedFunctorNatTrans]
  erw [reassoc_of% ht', worker_comp_fac]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 1
  apply congrArg DerivedCategory.Qh.map
  have hh := congr_app (congrArg (fun t ↦ NatTrans.mapHomotopyCategory t (.up ℤ)) h) X
  have hb : (NatTrans.mapHomotopyCategory (Functor.whiskerLeft F τ) (.up ℤ)).app X =
      (NatTrans.mapHomotopyCategory τ (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj X) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    rfl
  simpa only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app, hb] using hh

set_option backward.isDefEq.respectTransparency false in
private lemma worker_comp_normalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (I : CochainComplex C ℤ) :
    supportCompositionNormalization F G H e (Functor.rightDerivedFunctorCompIso' F G e) I := by
  unfold supportCompositionNormalization
  have h := worker_comp_fac F G H e ((HomotopyCategory.quotient _ _).obj I)
  unfold supportResolutionUnit
  simp only [Functor.map_comp, Category.assoc]
  erw [← G.rightDerivedFunctor.map_comp_assoc,
    Iso.hom_inv_id_app, G.rightDerivedFunctor.map_id, Category.id_comp]
  simp only [Category.id_comp]
  have hn := (Functor.rightDerivedFunctorCompIso' F G e).hom.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app I)
  dsimp only [Functor.comp_map] at hn
  erw [hn, reassoc_of% h]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom, NatTrans.mapHomotopyCategory_app]
  erw [Category.id_comp]
  rfl

private lemma worker_nat_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (τ : F ⟶ G)
    (I : CochainComplex C ℤ) :
    supportResolutionUnit F I ≫
        (Functor.rightDerivedFunctorNatTrans τ).app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app I) ≫
        supportResolutionUnit G I := by
  have h : F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) ≫
      (Functor.rightDerivedFunctorNatTrans τ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app
        ((HomotopyCategory.quotient _ _).obj I)) ≫
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) := by
    simp [Functor.rightDerivedFunctorNatTrans]
  unfold supportResolutionUnit
  simp only [Category.assoc]
  erw [(Functor.rightDerivedFunctorNatTrans τ).naturality, reassoc_of% h,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  rfl

private lemma worker_exact_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex C ℤ) :
    supportResolutionUnit F I ≫ F.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj I) = F.mapDerivedCategoryFactors.inv.app I := by
  have h := congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient _ _).obj I)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  unfold supportResolutionUnit
  simp only [Category.assoc]
  erw [F.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality,
    reassoc_of% h]
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app I)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have hh := F.mapDerivedCategoryFactorsh_hom_app I
  have hi := (F.mapDerivedCategoryFactorsh.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj I)).inv_hom_id
  change F.mapDerivedCategoryFactorsh.inv.app _ ≫
    F.mapDerivedCategoryFactorsh.hom.app _ = _ at hi
  rw [hh] at hi
  simp only [Iso.app_inv, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom, Functor.mapHomotopyCategoryFactors] at hi ⊢
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at hi
  erw [Category.id_comp, F.mapDerivedCategory.map_id, Category.id_comp]
  exact hi



private lemma worker_comp_forward
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesKInjectiveComplexes]
    (I : CochainComplex C ℤ) :
    supportResolutionUnit (F ⋙ G) I ≫
        (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj I) =
      supportResolutionUnit G ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        G.rightDerivedFunctor.map (supportResolutionUnit F I) := by
  have h := worker_comp_normalization F G (F ⋙ G) (Iso.refl _) I
  unfold supportCompositionNormalization at h
  have hid : Functor.rightDerivedFunctorNatTrans (𝟙 (F ⋙ G)) = 𝟙 _ := by
    simp [Functor.rightDerivedFunctorNatTrans]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.rightDerivedFunctorNatIso, Iso.refl_hom, hid] at h
  have hmap : (NatTrans.mapHomologicalComplex (𝟙 (F ⋙ G)) (.up ℤ)).app I = 𝟙 _ := rfl
  erw [hmap, DerivedCategory.Q.map_id, Category.id_comp, Category.comp_id] at h
  have hh := congrArg (fun t ↦ t ≫
    (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj I)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

private noncomputable def worker_derivedOpen
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (τ : H ⟶ F ⋙ G) :
    H.rightDerivedFunctor ⟶ F.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  Functor.rightDerivedFunctorNatTrans τ ≫
    (Functor.rightDerivedFunctorCompIso F G).hom ≫
      Functor.whiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.hom _

private lemma worker_open_normalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (τ : H ⟶ F ⋙ G) (I : CochainComplex C ℤ) :
    supportResolutionUnit H I ≫
        (Functor.rightDerivedFunctorNatTrans τ ≫
          (Functor.rightDerivedFunctorCompIso F G).hom ≫
          Functor.whiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.hom
            G.rightDerivedFunctor).app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app I) ≫
        supportResolutionUnit G ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app I) := by
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [reassoc_of% (worker_nat_normalization H (F ⋙ G) τ I),
    reassoc_of% (worker_comp_forward F G I)]
  rw [← G.rightDerivedFunctor.map_comp, worker_exact_normalization]


private noncomputable def worker_exchange
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    [HasKInjectiveResolutions B]
    (F : C ⥤ D) (R : D ⥤ E) (S : C ⥤ B) (H : B ⥤ E)
    [F.Additive] [R.Additive] [S.Additive] [H.Additive]
    [F.PreservesKInjectiveComplexes] [S.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : F ⋙ R ≅ S ⋙ H) :
    F.rightDerivedFunctor ⋙ R.mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ H.rightDerivedFunctor :=
  Functor.isoWhiskerLeft F.rightDerivedFunctor
      R.rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (Functor.rightDerivedFunctorCompIso F R).symm ≪≫
      Functor.rightDerivedFunctorNatIso e ≪≫
        Functor.rightDerivedFunctorCompIso S H ≪≫
          Functor.isoWhiskerRight S.rightDerivedFunctorIsoMapDerivedCategory _

set_option backward.isDefEq.respectTransparency false in
private lemma worker_exchange_normalization
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    [HasKInjectiveResolutions B]
    (F : C ⥤ D) (R : D ⥤ E) (S : C ⥤ B) (H : B ⥤ E)
    [F.Additive] [R.Additive] [S.Additive] [H.Additive]
    [F.PreservesKInjectiveComplexes] [S.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : F ⋙ R ≅ S ⋙ H) (I : CochainComplex C ℤ) :
    R.mapDerivedCategory.map (supportResolutionUnit F I) ≫
        (worker_exchange F R S H e).hom.app (DerivedCategory.Q.obj I) =
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((e.hom.mapHomologicalComplex (.up ℤ)).app I) ≫
        supportResolutionUnit H ((S.mapHomologicalComplex (.up ℤ)).obj I) ≫
        H.rightDerivedFunctor.map (S.mapDerivedCategoryFactors.inv.app I) := by
  apply (cancel_epi
    (R.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I))).mp
  simp only [worker_exchange, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.inv_hom_id_app_assoc]
  erw [R.rightDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  have hR := worker_exact_normalization R ((F.mapHomologicalComplex (.up ℤ)).obj I)
  have hR' : R.mapDerivedCategoryFactors.inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      R.rightDerivedFunctorIsoMapDerivedCategory.inv.app
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) =
      supportResolutionUnit R ((F.mapHomologicalComplex (.up ℤ)).obj I) := by
    rw [← hR, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  erw [reassoc_of% hR']
  have hc := worker_comp_forward F R I
  have hc' : supportResolutionUnit R ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      R.rightDerivedFunctor.map (supportResolutionUnit F I) ≫
        (Functor.rightDerivedFunctorCompIso F R).inv.app (DerivedCategory.Q.obj I) =
      supportResolutionUnit (F ⋙ R) I := by
    erw [← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  erw [reassoc_of% hc', reassoc_of% (worker_nat_normalization _ _ e.hom I),
    reassoc_of% (worker_comp_forward S H I)]
  rw [← H.rightDerivedFunctor.map_comp, worker_exact_normalization]


private instance worker_resolutionUnitIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (supportResolutionUnit F I) := by
  unfold supportResolutionUnit
  infer_instance

private lemma worker_nat_ext
    {C E : Type*} [Category C] [Category E] [Abelian C]
    [HasDerivedCategory C] [HasKInjectiveResolutions C]
    {F G : DerivedCategory C ⥤ E} (α β : F ⟶ G)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  apply NatTrans.ext
  funext M
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  apply (cancel_mono (G.map e.hom)).mp
  rw [← α.naturality, ← β.naturality, h I]


set_option backward.isDefEq.respectTransparency false in
private lemma worker_derived_unit_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (I : CochainComplex C ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj I) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map
          ((adj.unit.mapHomologicalComplex (.up ℤ)).app I) ≫
        supportResolutionUnit R ((L.mapHomologicalComplex (.up ℤ)).obj I) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient C (.up ℤ)).obj I)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors] at h
  simp only [Functor.map_comp] at h
  erw [L.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id] at h
  erw [R.rightDerivedFunctor.map_id, R.rightDerivedFunctor.map_id] at h
  simp only [Category.id_comp, Category.comp_id] at h
  unfold supportResolutionUnit
  simp only [Iso.app_inv, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [R.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  exact h



set_option backward.isDefEq.respectTransparency false in
private lemma worker_resolution_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {I J : CochainComplex C ℤ} (f : I ⟶ J) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
        supportResolutionUnit F J =
      supportResolutionUnit F I ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
  unfold supportResolutionUnit
  simp only [Category.assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  have hn := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map f)
  dsimp only [Functor.comp_map] at hn
  rw [Functor.mapHomotopyCategory_map] at hn
  erw [reassoc_of% hn]
  rw [← F.rightDerivedFunctor.map_comp, DerivedCategory.quotientCompQhIso_hom_naturality]
  rw [Functor.map_comp]
  rfl

private lemma worker_exact_comp_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (I : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj I) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app I := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G I
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
    (.up ℤ)).hom.app I = 𝟙 _ := rfl
  rw [hi] at h
  erw [DerivedCategory.Q.map_id, Category.comp_id] at h
  exact h

private lemma worker_exact_exchange_fac
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    (F : C ⥤ D) (R : D ⥤ E) (S : C ⥤ B) (H : B ⥤ E)
    [F.Additive] [R.Additive] [S.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ R ≅ S ⋙ H) (I : CochainComplex C ℤ) :
    ((Functor.mapDerivedCategoryCompIso F R).symm ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
          Functor.mapDerivedCategoryCompIso S H).hom.app (DerivedCategory.Q.obj I) ≫
      H.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app I) ≫
        H.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj I) =
      R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I) ≫
        R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((e.hom.mapHomologicalComplex (.up ℤ)).app I) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [worker_exact_comp_fac, Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F R).hom.app
    (DerivedCategory.Q.obj I))).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  erw [reassoc_of% (worker_exact_comp_fac F R I)]


set_option backward.isDefEq.respectTransparency false in
private lemma worker_unit_exchange
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory B] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    [HasKInjectiveResolutions B] [HasKInjectiveResolutions E]
    (L : C ⥤ D) (F : D ⥤ C) (L' : B ⥤ E) (F' : E ⥤ B)
    (r : C ⥤ B) (s : D ⥤ E)
    [L.Additive] [F.Additive] [L'.Additive] [F'.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [F.PreservesKInjectiveComplexes] [s.PreservesKInjectiveComplexes]
    (adj : L ⊣ F) (adj' : L' ⊣ F')
    (e : F ⋙ r ≅ s ⋙ F') (a : r ⋙ L' ≅ L ⋙ s)
    (hunit : ∀ X : C, r.map (adj.unit.app X) ≫ e.hom.app (L.obj X) ≫
      F'.map (a.inv.app X) = adj'.unit.app (r.obj X))
    (M : DerivedCategory C) :
    let aD := (Functor.mapDerivedCategoryCompIso r L').symm ≪≫
      Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso L s
    r.mapDerivedCategory.map (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
      (worker_exchange F r s F' e).hom.app (L.mapDerivedCategory.obj M) ≫
      F'.rightDerivedFunctor.map (aD.inv.app M) =
    adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app (r.mapDerivedCategory.obj M) := by
  let aD := (Functor.mapDerivedCategoryCompIso r L').symm ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso L s
  suffices hh :
      Functor.whiskerRight adj.mapDerivedCategoryRightDerivedAdjunction.unit r.mapDerivedCategory ≫
        Functor.whiskerLeft L.mapDerivedCategory (worker_exchange F r s F' e).hom ≫
        Functor.whiskerRight aD.inv F'.rightDerivedFunctor =
      Functor.whiskerLeft r.mapDerivedCategory adj'.mapDerivedCategoryRightDerivedAdjunction.unit by
    exact congr_app hh M
  apply worker_nat_ext
  intro I hI
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  apply (cancel_mono (F'.rightDerivedFunctor.map
    (L'.mapDerivedCategory.map (r.mapDerivedCategoryFactors.hom.app I) ≫
      L'.mapDerivedCategoryFactors.hom.app
        ((r.mapHomologicalComplex (.up ℤ)).obj I)))).mp
  simp only [Category.assoc]
  have hf := worker_exact_exchange_fac r L' L s a I
  change aD.hom.app (DerivedCategory.Q.obj I) ≫
    s.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app I) ≫
      s.mapDerivedCategoryFactors.hom.app _ = _ at hf
  have ha : aD.inv.app (DerivedCategory.Q.obj I) ≫
      L'.mapDerivedCategory.map (r.mapDerivedCategoryFactors.hom.app I) ≫
        L'.mapDerivedCategoryFactors.hom.app _ =
      s.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app I) ≫
        s.mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map
            ((a.inv.mapHomologicalComplex (.up ℤ)).app I) := by
    apply (cancel_epi (aD.hom.app
      (DerivedCategory.Q.obj I))).mp
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    simp only [Category.assoc]
    erw [reassoc_of% hf, ← DerivedCategory.Q.map_comp]
    have he : (a.hom.mapHomologicalComplex (.up ℤ)).app I ≫
        (a.inv.mapHomologicalComplex (.up ℤ)).app I = 𝟙 _ := by
      apply HomologicalComplex.Hom.ext
      funext n
      exact a.hom_inv_id_app (I.X n)
    erw [he, DerivedCategory.Q.map_id, Category.comp_id]
  rw [← F'.rightDerivedFunctor.map_comp, ha]
  simp only [Functor.map_comp]
  have hn := (worker_exchange F r s F' e).hom.naturality (L.mapDerivedCategoryFactors.hom.app I)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  rw [← r.mapDerivedCategory.map_comp_assoc,
    worker_derived_unit_normalization L F adj I, Functor.map_comp]
  have hr := worker_exchange_normalization F r s F' e
    ((L.mapHomologicalComplex (.up ℤ)).obj I)
  change r.mapDerivedCategory.map (supportResolutionUnit F _) ≫
    (worker_exchange F r s F' e).hom.app _ = _ at hr
  simp only [Category.assoc]
  erw [reassoc_of% hr]
  erw [worker_map_inv_hom_assoc F'.rightDerivedFunctor
    (s.mapDerivedCategoryFactors.app ((L.mapHomologicalComplex (.up ℤ)).obj I))]
  have hη :
      (r.mapHomologicalComplex (.up ℤ)).map
          ((adj.unit.mapHomologicalComplex (.up ℤ)).app I) ≫
        (e.hom.mapHomologicalComplex (.up ℤ)).app
          ((L.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (F'.mapHomologicalComplex (.up ℤ)).map
          ((a.inv.mapHomologicalComplex (.up ℤ)).app I) =
      (adj'.unit.mapHomologicalComplex (.up ℤ)).app
        ((r.mapHomologicalComplex (.up ℤ)).obj I) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hunit (I.X n)
  have hres := worker_resolution_naturality F'
    ((a.inv.mapHomologicalComplex (.up ℤ)).app I)
  erw [← hres]
  erw [r.mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc]
  erw [Category.assoc, hη]
  have hu := worker_derived_unit_normalization L' F' adj'
    ((r.mapHomologicalComplex (.up ℤ)).obj I)
  have hun := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (r.mapDerivedCategoryFactors.hom.app I)
  dsimp only [Functor.comp_map, Functor.id_map] at hun
  erw [← reassoc_of% hun]
  erw [hu]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma worker_open_square
    {C D B E U : Type*}
    [Category C] [Category D] [Category B] [Category E] [Category U]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E] [Abelian U]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]
    [HasDerivedCategory E] [HasDerivedCategory U]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    [HasKInjectiveResolutions B] [HasKInjectiveResolutions E]
    (F : C ⥤ D) (R : D ⥤ E) (S : C ⥤ B) (H : B ⥤ E)
    (K : D ⥤ U) (P : C ⥤ U) (K' : E ⥤ U) (P' : B ⥤ U)
    [F.Additive] [R.Additive] [S.Additive] [H.Additive]
    [K.Additive] [P.Additive] [K'.Additive] [P'.Additive]
    [F.PreservesKInjectiveComplexes] [R.PreservesKInjectiveComplexes]
    [S.PreservesKInjectiveComplexes] [H.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (eb : F ⋙ K ≅ P) (eb' : H ⋙ K' ≅ P') (e : F ⋙ R ≅ S ⋙ H)
    (τ : K ⟶ R ⋙ K') (σ : P ⟶ S ⋙ P')
    (h : supportRestrictionSquare F R S H K P K' P' eb.hom e.hom eb'.hom τ σ) :
    supportRestrictionSquare F.rightDerivedFunctor R.mapDerivedCategory
      S.mapDerivedCategory H.rightDerivedFunctor K.rightDerivedFunctor P.rightDerivedFunctor
      K'.rightDerivedFunctor P'.rightDerivedFunctor
      (Functor.rightDerivedFunctorCompIso' F K eb).hom (worker_exchange F R S H e).hom
      (Functor.rightDerivedFunctorCompIso' H K' eb').hom
      (worker_derivedOpen R K' K τ) (worker_derivedOpen S P' P σ) := by
  unfold supportRestrictionSquare at h ⊢
  apply worker_nat_ext
  intro I hI
  apply (cancel_epi
    (supportResolutionUnit K ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      K.rightDerivedFunctor.map (supportResolutionUnit F I))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  have hb := worker_comp_normalization F K P eb I
  unfold supportCompositionNormalization at hb
  erw [reassoc_of% hb]
  have hnet := (worker_derivedOpen R K' K τ).naturality (supportResolutionUnit F I)
  dsimp only [Functor.comp_map] at hnet
  erw [reassoc_of% hnet]
  have het := worker_open_normalization R K' K τ
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  change supportResolutionUnit K _ ≫ (worker_derivedOpen R K' K τ).app _ = _ at het
  erw [reassoc_of% het]
  erw [← K'.rightDerivedFunctor.map_comp_assoc
    (R.mapDerivedCategory.map (supportResolutionUnit F I))
    ((worker_exchange F R S H e).hom.app (DerivedCategory.Q.obj I))]
  erw [worker_exchange_normalization]
  simp only [Functor.map_comp, Category.assoc]
  erw [worker_map_inv_hom_assoc K'.rightDerivedFunctor
    (R.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj I))]
  have hn := (Functor.rightDerivedFunctorCompIso' H K' eb').hom.naturality
    (S.mapDerivedCategoryFactors.inv.app I)
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  have hres := worker_resolution_naturality K'
    ((e.hom.mapHomologicalComplex (.up ℤ)).app I)
  erw [← reassoc_of% hres]
  have hb' := worker_comp_normalization H K' P' eb'
    ((S.mapHomologicalComplex (.up ℤ)).obj I)
  unfold supportCompositionNormalization at hb'
  erw [reassoc_of% hb']
  have hpro := worker_open_normalization S P' P σ I
  change supportResolutionUnit P I ≫ (worker_derivedOpen S P' P σ).app _ = _ at hpro
  erw [hpro]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  have hh' : (eb.hom.mapHomologicalComplex (.up ℤ)).app I ≫
      (σ.mapHomologicalComplex (.up ℤ)).app I =
    (τ.mapHomologicalComplex (.up ℤ)).app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      (K'.mapHomologicalComplex (.up ℤ)).map ((e.hom.mapHomologicalComplex (.up ℤ)).app I) ≫
        (eb'.hom.mapHomologicalComplex (.up ℤ)).app
          ((S.mapHomologicalComplex (.up ℤ)).obj I) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congr_app h (I.X n)
  rw [hh']

private lemma supportFullComplementEmpty_worker (T : Scheme.{u}) :
    IsEmpty (𝟙 T : T ⟶ T).openComplement.toScheme := by
  constructor
  intro x
  exact x.property ⟨x.val, rfl⟩

private noncomputable def worker_complementMap {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] (V : T.Opens) :
    (pullback.snd i V.ι).openComplement.toScheme ⟶ i.openComplement.toScheme :=
  IsOpenImmersion.lift i.openComplement.ι
    ((pullback.snd i V.ι).openComplement.ι ≫ V.ι) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      change ¬ V.ι x.val ∈ Set.range i
      have hx := x.property
      change x.val ∉ Set.range (pullback.snd i V.ι) at hx
      rw [Scheme.Pullback.range_snd] at hx
      exact hx)

private noncomputable def worker_openEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] (V : T.Opens) :
    supportEt A i ⟶ supportRestrictEt A V ⋙ supportEt A (pullback.snd i V.ι) where
  app F := kernel.lift _
    ((supportForgetEt A i).app F ≫ (supportSectionRestrictionEt A V).app F) (by
      dsimp [supportForgetEt, supportSectionRestrictionEt]
      let k : Scheme.Etale.mk
          ((pullback.snd i V.ι).openComplement.ι ≫ V.ι) ⟶
          Scheme.Etale.mk i.openComplement.ι :=
        MorphismProperty.Over.homMk (worker_complementMap i V)
          (IsOpenImmersion.lift_fac _ _ _)
      have he : k ≫ Etale.supportRestrictionArrow i =
          MorphismProperty.Over.homMk
            (pullback.snd i V.ι).openComplement.ι (by simp) ≫
              (MorphismProperty.Over.homMk V.ι (by change V.ι ≫ 𝟙 T = _; simp) :
                Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk (𝟙 T)) := by
        apply MorphismProperty.Over.Hom.ext
        exact IsOpenImmersion.lift_fac _ _ _
      change kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op) ≫
        F.obj.map _ ≫ F.obj.map _ = 0
      change kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op) ≫
        F.obj.map (MorphismProperty.Over.homMk V.ι
          (by change V.ι ≫ 𝟙 T = _; simp) :
          Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk (𝟙 T)).op ≫
        F.obj.map (MorphismProperty.Over.homMk
          (pullback.snd i V.ι).openComplement.ι (by simp) :
          Scheme.Etale.mk ((pullback.snd i V.ι).openComplement.ι ≫ V.ι) ⟶
            Scheme.Etale.mk V.ι).op = 0
      rw [← F.obj.map_comp, ← op_comp, ← he, op_comp, F.obj.map_comp,
        ← Category.assoc, kernel.condition, zero_comp])
  naturality {F G} f := by
    apply (cancel_mono (kernel.ι _)).mp
    dsimp [supportEt, Sheaf.supportedSectionsFunctor, kernel.map]
    simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    exact (supportForgetEt A i ≫ supportSectionRestrictionEt A V).naturality f

private noncomputable def worker_openPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] (V : T.Opens) :
    supportPro A i ⟶ supportRestrictPro A V ⋙ supportPro A (pullback.snd i V.ι) where
  app F := kernel.lift _
    ((supportForgetPro A i).app F ≫ (supportSectionRestrictionPro A V).app F) (by
      dsimp [supportForgetPro, supportSectionRestrictionPro]
      let k : Scheme.ProEt.mk
          ((pullback.snd i V.ι).openComplement.ι ≫ V.ι) ⟶
          Scheme.ProEt.mk i.openComplement.ι :=
        MorphismProperty.Over.homMk (worker_complementMap i V)
          (IsOpenImmersion.lift_fac _ _ _)
      have he : k ≫ supportRestrictionArrow i =
          MorphismProperty.Over.homMk
            (pullback.snd i V.ι).openComplement.ι (by simp) ≫
              (MorphismProperty.Over.homMk V.ι (by change V.ι ≫ 𝟙 T = _; simp) :
                Scheme.ProEt.mk V.ι ⟶ Scheme.ProEt.mk (𝟙 T)) := by
        apply MorphismProperty.Over.Hom.ext
        exact IsOpenImmersion.lift_fac _ _ _
      change kernel.ι (F.obj.map (supportRestrictionArrow i).op) ≫
        F.obj.map _ ≫ F.obj.map _ = 0
      change kernel.ι (F.obj.map (supportRestrictionArrow i).op) ≫
        F.obj.map (MorphismProperty.Over.homMk V.ι
          (by change V.ι ≫ 𝟙 T = _; simp) :
          Scheme.ProEt.mk V.ι ⟶ Scheme.ProEt.mk (𝟙 T)).op ≫
        F.obj.map (MorphismProperty.Over.homMk
          (pullback.snd i V.ι).openComplement.ι (by simp) :
          Scheme.ProEt.mk ((pullback.snd i V.ι).openComplement.ι ≫ V.ι) ⟶
            Scheme.ProEt.mk V.ι).op = 0
      rw [← F.obj.map_comp, ← op_comp, ← he, op_comp, F.obj.map_comp,
        ← Category.assoc, kernel.condition, zero_comp])
  naturality {F G} f := by
    apply (cancel_mono (kernel.ι _)).mp
    dsimp [supportPro, Sheaf.supportedSectionsFunctor, kernel.map]
    simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    exact (supportForgetPro A i ≫ supportSectionRestrictionPro A V).naturality f

private instance worker_nuKI (T : Scheme.{u}) :
    (supportNu A T).PreservesKInjectiveComplexes :=
  (comparisonAdjunction (ModuleCat.{u + 1} A) T).preservesKInjectiveComplexes

private instance worker_restrictEtKI {T : Scheme.{u}} (V : T.Opens) :
    (supportRestrictEt A V).PreservesKInjectiveComplexes :=
  (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) V.ι).preservesKInjectiveComplexes

private instance worker_restrictProKI {T : Scheme.{u}} (V : T.Opens) :
    (supportRestrictPro A V).PreservesKInjectiveComplexes :=
  (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) V.ι).preservesKInjectiveComplexes

private noncomputable abbrev worker_b {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :
    (supportNu A T).rightDerivedFunctor ⋙ (supportEt A i).rightDerivedFunctor ≅
      (supportPro A i).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' _ _ (supportKernelIdentity A i)

private noncomputable abbrev worker_g (T : Scheme.{u}) :
    (supportNu A T).rightDerivedFunctor ⋙ (supportEvalEt A T).rightDerivedFunctor ≅
      (supportEvalPro A T).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' _ _ (supportEvaluationIdentity A T)

private lemma worker_open_coherence {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] (V : T.Opens) :
    supportRestrictionSquare (supportNu A T) (supportRestrictEt A V)
      (supportRestrictPro A V) (supportNu A V) (supportEt A i) (supportPro A i)
      (supportEt A (pullback.snd i V.ι)) (supportPro A (pullback.snd i V.ι))
      (supportKernelIdentity A i).hom (supportOpenIdentity A V).hom
      (supportKernelIdentity A (pullback.snd i V.ι)).hom
      (worker_openEt A i V) (worker_openPro A i V) := by
  unfold supportRestrictionSquare
  apply NatTrans.ext
  funext M
  apply (cancel_mono (kernel.ι
    (((supportRestrictPro A V).obj M).obj.map
      (supportRestrictionArrow (pullback.snd i V.ι)).op))).mp
  dsimp [worker_openPro, worker_openEt, supportEt, supportPro, supportNu,
    Sheaf.supportedSectionsFunctor, supportKernelIdentity, supportOpenIdentity, kernel.map]
  simp only [Category.assoc, kernel.lift_ι,
    Category.id_comp, Category.comp_id]
  have hι : kernel.ι
      (((supportRestrictPro A V).obj M).obj.map
        (supportRestrictionArrow (pullback.snd i V.ι)).op) =
    kernel.ι
      (((supportNu A V).obj ((supportRestrictPro A V).obj M)).obj.map
        (Etale.supportRestrictionArrow (pullback.snd i V.ι)).op) := by
    rfl
  rw [hι, kernel.lift_ι, kernel.lift_ι]
  rfl

private noncomputable abbrev worker_derivedOpenEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] (V : T.Opens) :
    (supportEt A i).rightDerivedFunctor ⟶
      (supportRestrictEt A V).mapDerivedCategory ⋙
        (supportEt A (pullback.snd i V.ι)).rightDerivedFunctor :=
  worker_derivedOpen _ _ _ (worker_openEt A i V)


private noncomputable abbrev worker_derivedOpenPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] (V : T.Opens) :
    (supportPro A i).rightDerivedFunctor ⟶
      (supportRestrictPro A V).mapDerivedCategory ⋙
        (supportPro A (pullback.snd i V.ι)).rightDerivedFunctor :=
  worker_derivedOpen _ _ _ (worker_openPro A i V)


private noncomputable abbrev worker_rho {T : Scheme.{u}} (V : T.Opens) :
    (supportNu A T).rightDerivedFunctor ⋙ (supportRestrictEt A V).mapDerivedCategory ≅
      (supportRestrictPro A V).mapDerivedCategory ⋙ (supportNu A V).rightDerivedFunctor :=
  worker_exchange _ _ _ _ (supportOpenIdentity A V)


attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory supportResolutionUnit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Supported sections commute canonically with etale/pro-etale direct image, for
all unbounded complexes over a finite commutative ring, with identity K-injective
normalization, forgetting supports, arbitrary open restriction, derived unit
compatibility, and the full-support final-object comparison.
Source: blueprint main-20261015, lem-pur-kunneth-supported.proof.md paragraph 4;
Stacks Tags 099R, 070K, 070Y, 08BJ and 08FI
(blueprint: lem-pur-derived-support-comparison-direct-image).

Proof:
1. Use the existing Grothendieck-abelian K-injective resolutions and canonical
   unbounded right-derived-functor composition isomorphism. The comparison right
   adjoint preserves K-injectives because its left adjoint is exact. The literal
   support-kernel and evaluation identities give b and g.
2. The defining composite-derived-unit factorization, transported from the homotopy
   category to complexes, proves both normalization equations. Functoriality in the
   second additive functor proves compatibility with forgetting supports.
3. Open restriction has exact extension by zero as left adjoint on both sites, so
   it preserves K-injectives. It also has a right adjoint and hence is exact.
   The literal restriction/direct-image identity and the canonical composition
   isomorphisms therefore give rho and its normalization.
4. Construct ordinary open restriction by the kernel universal property. The
   complement of the pulled-back support maps to the original complement, so
   restricting a supported section gives a supported section. The pro-etale map
   is the same map under the literal direct-image identity. Kernel inclusion
   proves the section equations and their comparison square.
5. Derive these ordinary maps using the composite-derived-functor and exact-functor
   comparisons. Their unit equations follow from the defining factorizations.
   Check the open square on K-injective representatives, cancel their invertible
   resolution units, and reduce both sides to the ordinary kernel square.
6. Use comparisonPullbackOpenUnit for the specified underived inverse-image
   comparison. The canonical derived adjunction's derived-unit factorization
   expresses its unit by the underived unit and the right-derived resolution unit.
   Combine this with rho normalization and exact-functor comparison naturality;
   testing on K-injective representatives proves the derived unit square.
7. For full support the complement is empty. The empty-cover sheaf condition
   makes its sections zero, so the kernel inclusion is an isomorphism on each
   site. Deriving preserves this isomorphism; the forgetting square identifies
   b with the final-object comparison g. -/
theorem derivedSupportDirectImageComparison [Finite A] :
    Nonempty (DerivedSupportDirectImageComparison A) := by
  refine ⟨{
    b := worker_b A
    g := worker_g A
    kernel_normalization := ?_
    final_normalization := ?_
    forget := ?_
    full_support := ?_
    openEt := worker_openEt A
    openEt_sections := ?_
    derivedOpenEt := worker_derivedOpenEt A
    derivedOpenEt_normalization := ?_
    openPro := worker_openPro A
    openPro_sections := ?_
    derivedOpenPro := worker_derivedOpenPro A
    derivedOpenPro_normalization := ?_
    rho := worker_rho A
    rho_normalization := ?_
    open_square := ?_
    unit_square := ?_
  }⟩
  · intro C T i hi J hJ
    unfold worker_b
    exact worker_comp_normalization (supportNu A T) (supportEt A i)
      (supportPro A i) (supportKernelIdentity A i) J
  · intro T J hJ
    exact worker_comp_normalization (supportNu A T) (supportEvalEt A T)
      (supportEvalPro A T) (supportEvaluationIdentity A T) J
  · intro C T i hi
    exact worker_comp_nat (supportNu A T) (supportEt A i) (supportEvalEt A T)
      (supportPro A i) (supportEvalPro A T) (supportKernelIdentity A i)
      (supportEvaluationIdentity A T) (supportForgetEt A i) (supportForgetPro A i) (by rfl)
  · intro T
    let : IsEmpty (𝟙 T : T ⟶ T).openComplement.toScheme :=
      supportFullComplementEmpty_worker T
    let : IsEmpty (Scheme.Etale.mk (𝟙 T : T ⟶ T).openComplement.ι).left :=
      supportFullComplementEmpty_worker T
    let : IsEmpty (Scheme.ProEt.mk (𝟙 T : T ⟶ T).openComplement.ι).left :=
      supportFullComplementEmpty_worker T
    have het : IsIso (supportForgetEt A (𝟙 T)) := by
      apply (NatTrans.isIso_iff_isIso_app _).mpr
      intro F
      change IsIso (kernel.ι (F.obj.map (Etale.supportRestrictionArrow (𝟙 T)).op))
      have hz := (Scheme.Etale.isTerminalSectionsOfIsEmpty F
        (Scheme.Etale.mk (𝟙 T : T ⟶ T).openComplement.ι)).isZero
      exact kernel.ι_of_zero (hz.eq_of_tgt _ 0)
    have hpro : IsIso (supportForgetPro A (𝟙 T)) := by
      apply (NatTrans.isIso_iff_isIso_app _).mpr
      intro F
      change IsIso (kernel.ι (F.obj.map (supportRestrictionArrow (𝟙 T)).op))
      have hz := (Scheme.ProEt.isTerminalSectionsOfIsEmpty F
        (Scheme.ProEt.mk (𝟙 T : T ⟶ T).openComplement.ι)).isZero
      exact kernel.ι_of_zero (hz.eq_of_tgt _ 0)
    constructor <;> infer_instance
  · intro C T i hi V
    apply NatTrans.ext
    funext F
    exact kernel.lift_ι _ _ _
  · intro C T i hi V I hI
    exact worker_open_normalization _ _ _ (worker_openEt A i V) I
  · intro C T i hi V
    apply NatTrans.ext
    funext F
    exact kernel.lift_ι _ _ _
  · intro C T i hi V I hI
    exact worker_open_normalization _ _ _ (worker_openPro A i V) I
  · intro T V J hJ
    exact worker_exchange_normalization _ _ _ _ (supportOpenIdentity A V) J
  · intro C T i hi V
    exact worker_open_square (supportNu A T) (supportRestrictEt A V)
      (supportRestrictPro A V) (supportNu A V) (supportEt A i) (supportPro A i)
      (supportEt A (pullback.snd i V.ι)) (supportPro A (pullback.snd i V.ι))
      (supportKernelIdentity A i) (supportKernelIdentity A (pullback.snd i V.ι))
      (supportOpenIdentity A V) (worker_openEt A i V) (worker_openPro A i V)
      (worker_open_coherence A i V)
  · intro T V M
    exact worker_unit_exchange
      (comparisonUpperStar (ModuleCat.{u + 1} A) T) (supportNu A T)
      (comparisonUpperStar (ModuleCat.{u + 1} A) V) (supportNu A V)
      (supportRestrictEt A V) (supportRestrictPro A V)
      (comparisonAdjunction (ModuleCat.{u + 1} A) T)
      (comparisonAdjunction (ModuleCat.{u + 1} A) V)
      (supportOpenIdentity A V) (supportOpenPullback A V)
      (comparisonPullbackOpenUnit A V.ι) M

end AlgebraicGeometry.ProEtale
