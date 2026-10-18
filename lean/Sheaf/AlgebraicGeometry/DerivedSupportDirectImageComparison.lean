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

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors

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

variable (A : Type (u + 1)) [CommRing A]

/-- The existing kernel-of-restriction functor with fixed scalar coefficients.
Source: blueprint paragraph 4 and the kernel formula of def-pur-support-cohomology
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor (T.smallEtaleTopology) (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)

/-- Evaluation on the final scheme, the concrete global-sections model.
Source: Stacks Tag 099R, final-object comparison
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportEvalEt (T : Scheme.{u}) :=
  sheafToPresheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))

/-- The kernel inclusion, namely forgetting supports.
Source: blueprint paragraph 4, support localization diagram
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportForgetEt {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : supportEt A i ⟶ supportEvalEt A T where
  app F := kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op)
  naturality f := by simp [supportEt, Sheaf.supportedSectionsFunctor]

/-- The existing kernel-of-restriction functor with fixed scalar coefficients.
Source: blueprint paragraph 4 and the kernel formula of def-pur-support-cohomology
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
    (supportRestrictionArrow i)

/-- Evaluation on the final scheme, the concrete global-sections model.
Source: Stacks Tag 099R, final-object comparison
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportEvalPro (T : Scheme.{u}) :=
  sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))

/-- The kernel inclusion, namely forgetting supports.
Source: blueprint paragraph 4, support localization diagram
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportForgetPro {C T : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : supportPro A i ⟶ supportEvalPro A T where
  app F := kernel.ι (F.obj.map (supportRestrictionArrow i).op)
  naturality f := by simp [supportPro, Sheaf.supportedSectionsFunctor]

/-- The original-site direct image, restriction along the etale inclusion.
Source: Stacks Tag 099R (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable abbrev supportNu (T : Scheme.{u}) :=
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
noncomputable abbrev supportDerivedAdjunction (T : Scheme.{u}) :=
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
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The literal final-object direct-image identity.
Source: Stacks Tag 099R (blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportEvaluationIdentity (T : Scheme.{u}) :
    supportNu A T ⋙ supportEvalEt A T ≅ supportEvalPro A T :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The literal open-restriction/direct-image identity.
Source: Stacks Tags 099R and 08FI
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportOpenIdentity {T : Scheme.{u}} (V : T.Opens) :
    supportNu A T ⋙ supportRestrictEt A V ≅
      supportRestrictPro A V ⋙ supportNu A V :=
  Iso.refl _

/-- The canonical comparison-pullback isomorphism in open restriction form.
Source: lem-weil-pbc-comparison-pullback, its adjunction-mate normalization
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportOpenPullback {T : Scheme.{u}} (V : T.Opens) :
    supportRestrictEt A V ⋙ comparisonUpperStar (ModuleCat.{u + 1} A) V ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportRestrictPro A V :=
  Functor.isoWhiskerRight
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) V.ι).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) V.ι ≪≫
      Functor.isoWhiskerLeft _
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) V.ι)


/-- The same canonical inverse-image comparison on unbounded derived categories.
Source: lem-weil-pbc-comparison-pullback and Stacks Tag 015F
(blueprint: lem-pur-derived-support-comparison-direct-image). -/
noncomputable def supportDerivedOpenPullback {T : Scheme.{u}} (V : T.Opens) :=
  (Functor.mapDerivedCategoryCompIso (supportRestrictEt A V)
    (comparisonUpperStar (ModuleCat.{u + 1} A) V)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (supportOpenPullback A V) ≪≫
      Functor.mapDerivedCategoryCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} A) T) (supportRestrictPro A V)

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
    supportResolutionUnit (supportEt A i)
        (((supportNu A T).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
      (supportEt A i).rightDerivedFunctor.map (supportResolutionUnit (supportNu A T) J) ≫
      (b i).hom.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map
        (((supportKernelIdentity A i).hom.mapHomologicalComplex (ComplexShape.up ℤ)).app J) ≫
      supportResolutionUnit (supportPro A i) J
  /-- Identity on the indicated K-injective section complex. -/
  final_normalization : ∀ (T : Scheme.{u})
      (J : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ)
      [J.IsKInjective],
    supportResolutionUnit (supportEvalEt A T)
        (((supportNu A T).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
      (supportEvalEt A T).rightDerivedFunctor.map (supportResolutionUnit (supportNu A T) J) ≫
      (g T).hom.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map
        (((supportEvaluationIdentity A T).hom.mapHomologicalComplex (ComplexShape.up ℤ)).app J) ≫
      supportResolutionUnit (supportEvalPro A T) J
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
    (b i).hom ≫ derivedOpenPro i V =
      Functor.whiskerLeft (supportNu A T).rightDerivedFunctor (derivedOpenEt i V) ≫
        Functor.whiskerRight (rho V).hom
          (supportEt A (pullback.snd i V.ι)).rightDerivedFunctor ≫
        Functor.whiskerLeft (supportRestrictPro A V).mapDerivedCategory
          (b (pullback.snd i V.ι)).hom
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

/-- Supported sections commute canonically with etale/pro-etale direct image, for
all unbounded complexes over a finite commutative ring, with identity K-injective
normalization, forgetting supports, arbitrary open restriction, derived unit
compatibility, and the full-support final-object comparison.
Source: blueprint main-20261015, lem-pur-kunneth-supported.proof.md paragraph 4;
Stacks Tags 099R, 070K, 070Y, 08BJ and 08FI
(blueprint: lem-pur-derived-support-comparison-direct-image).

Proof:
1. Use prop-pur-kinjective-resolutions-exist on small site representatives.
   The support kernels and direct image are additive, so the construction of
   lem-weil-pbc-kinjective-total-derived supplies their unbounded right derived functors.
2. Comparison inverse image is exact. Its right adjoint therefore preserves
   K-injectives by lem-weil-pbc-right-adjoint-preserves-kinjective. On a K-injective J,
   direct image retains exactly J(T), J(T minus C), their restrictions and differentials.
   The identity of these kernel complexes gives b and its normalization.
3. By lem-weil-pbc-kinjective-hom-derived every derived morphism between such models
   is a unique homotopy class of chain maps. Kernel restriction respects homotopies.
   Thus b is independent of resolution and natural.
4. Identify open inverse images with slice restriction using
   lem-weil-pbc-etale-site-localization-open, lem-weil-pbc-etale-inverse-image-restriction,
   lem-weil-proetale-weakly-etale-localization and
   lem-sfb-proetale-object-inverse-image-restriction. By lem-pur-kinjective-restrict-localized
   restriction preserves K-injectives. The sectionwise direct-image identity gives rho.
5. Forgetting supports is kernel inclusion. Open restriction sends a kernel section s
   to its restriction to V, which still vanishes on V minus C_V. Both comparison squares
   are identity squares on these complexes. They descend by Step 3.
6. Apply lem-pur-comparison-pullback-open-unit: the canonical inverse-image comparison
   and the literal direct-image restriction identity intertwine underived units.
7. Exact inverse image descends termwise by lem-weil-pbc-exact-functor-derived-factorization.
   The canonical derived adjunction of lem-pc-derived-adjoint-functors is computed by the
   K-injective Hom bijections. The adjunct of a resolution r is the ordinary unit followed
   by direct image of r. Restrict r and apply Step 6; the two resulting maps are exactly
   the restricted derived units. This proves unit_square for arbitrary unbounded M.
8. For C=T the complement is empty. The sheaf axiom for the empty covering makes its
   section module zero, hence its kernel is J(T). The b normalization is therefore the
   same identity as the final-object comparison g. The forget square identifies them.
-/
theorem derivedSupportDirectImageComparison [Finite A] :
    Nonempty (DerivedSupportDirectImageComparison A) := by
  sorry

end AlgebraicGeometry.ProEtale
