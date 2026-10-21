/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.PuritySupportCommonInjectives
public import Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison

/-!
# The specified comparisons on the common section model

Source: Stacks Project, Tag 09XP, section-cohomology-support, and the
agent-formulated refinement of the final comparison sentence of blueprint
main-20261015, thm-pur-rank-one-local-calculation
(blueprint: lem-pur-support-comparison-section-model).

The computation isomorphisms below are characterized by the given augmentations
and the canonical right-derived units. The comparison on the common complex is
the literal direct-image identity, including on the support kernel.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The ordinary unit augmentation for any bounded-below source complex.
Source: Tag 09XP and the specified augmentation a in the node
(blueprint: lem-pur-support-comparison-section-model). -/
def sectionModelAugmentation
    (M : CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj M ⟶ J) :
    M ⟶ (comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J :=
  ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex (comparisonAdjunction (ModuleCat.{u + 1} A) T).unit
      (.up ℤ)).app M.obj ≫
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex (.up ℤ)).map
        h.hom)

/-- The localized resolution arrow with its canonical exact-inverse-image factor.
Source: Tag 09XP, augmentations h and a and their derived computations
(blueprint: lem-pur-support-comparison-section-model). -/
def sectionModelLocalizedResolution
    (M : CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj M ⟶ J) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.quotient _).obj M) ≫ DerivedCategory.Plus.Q.map h

/-- Canonical injective computations representing a specified comparison by the
sectionwise identity. The equations fix both isomorphisms using the augmentations;
the last equation is the asserted representation, not a choice of comparison.
Source: Tag 09XP, common section and support-kernel model
(blueprint: lem-pur-support-comparison-section-model). -/
structure SupportSectionModelComputation
    (M : CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj M ⟶ J)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A)
    (H : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A)
    [G.Additive] [H.Additive]
    (e : comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙ G ≅ H)
    (c : G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj M) ⟶
      H.rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj
          (DerivedCategory.Plus.Q.obj M))) where
  /-- Etale computation using exactly the augmentation a. -/
  et : DerivedCategory.Plus.Q.obj
      (G.mapCochainComplexPlus.obj
        ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J)) ≅
    G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj M)
  /-- Pro-etale computation using exactly the augmentation h. -/
  pro : DerivedCategory.Plus.Q.obj (H.mapCochainComplexPlus.obj J) ≅
    H.rightDerivedFunctorPlus.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj
        (DerivedCategory.Plus.Q.obj M))
  /-- The etale computation is the canonical right-derived-unit computation. -/
  et_normalization : et.hom ≫ G.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (sectionModelAugmentation T A M J h)) =
    G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient _).obj
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J))
  /-- The pro-etale computation is the canonical right-derived-unit computation. -/
  pro_normalization : pro.hom ≫ H.rightDerivedFunctorPlus.map
      (sectionModelLocalizedResolution T A M J h) =
    H.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient _).obj J)
  /-- The specified comparison has the direct-image identity as representative. -/
  represents : et.hom ≫ c =
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app J.obj)) ≫ pro.hom

/-- Global comparison with the identity-functor transport already removed.
Source: lem-weil-pbc-comparison-global-cohomology, canonical global comparison
(blueprint: lem-pur-support-comparison-section-model). -/
def sectionModelGlobalComparison :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    finiteComparisonGlobalSections T A

/-- Restrict the source complex to the specified open complement.
Source: Tag 09XP, restriction to V
(blueprint: lem-pur-support-comparison-section-model). -/
abbrev sectionModelOpenSource {C : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (M : CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (supportRestrictEt A i.openComplement).mapCochainComplexPlus.obj M

/-- Restrict the injective complex to the specified open complement.
Source: Tag 09XP, restriction to V
(blueprint: lem-pur-support-comparison-section-model). -/
abbrev sectionModelOpenResolution {C : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  (supportRestrictPro A i.openComplement).mapCochainComplexPlus.obj J

/-- The restricted augmentation uses exactly beta followed by restriction of h.
Source: Tag 09XP, and canonical comparison-pullback, Tag 03CF
(blueprint: lem-pur-support-comparison-section-model). -/
def sectionModelOpenAugmentation {C : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (M : CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj M ⟶ J) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) i.openComplement.toScheme).mapCochainComplexPlus.obj
         (sectionModelOpenSource T A i M) ⟶
      sectionModelOpenResolution T A i J :=
  ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex
      (comparisonPullbackOpenUnitGamma A i.openComplement.ι).hom (.up ℤ)).app M.obj ≫
      ((supportRestrictPro A i.openComplement).mapHomologicalComplex (.up ℤ)).map h.hom)

/-- The three named comparisons are represented by the identities on the common
section complexes and the common kernel, with the given augmentations.
Source: Tag 09XP, kernel restriction construction, and the agent-formulated comparison
refinement in the node (blueprint: lem-pur-support-comparison-section-model).

Proof:
1. Direct image evaluates J on the very same etale objects and arrows, hence gives
identical section complexes, restriction arrows and support kernels, with identical
kernel inclusions (def-pur-support-cohomology).
2. Apply lem-pur-comparison-pullback-open-unit and cancel beta inverse. This gives
exactly the ordinary unit equation below, with its sectionwise direct-image identity.
3. Use the injective-computation normalization e Qa = eta from the hypotheses.
Naturality of lem-weil-pbc-right-derived-plus-injective identifies RΓ(eta) with the
identity on I(T). The full-support normalization of
lem-pur-derived-support-comparison-direct-image identifies the second factor with
the identity I(T) = J(T). Their composite is the specified global comparison of
lem-weil-pbc-comparison-global-cohomology.
4. Restriction preserves injectives (lem-weil-pbc-proetale-restriction-injectives).
The restricted augmentation is beta followed by restriction of h. The ordinary unit
equation identifies its etale augmentation with restriction of a. Repeat step 3 on V.
5. Repeat step 3 for the additive support-kernel functor. Bounded-below injectives
are K-injective (lem-weil-pbc-bounded-below-injectives-kinjective), so the specified
kernel normalization of b gives the displayed factorization of the named c, and
its representative is the identity on the kernel. This uses b's normalization,
not merely compatibility with the other two terms.
6. The two ordinary identity maps preserve the actual restriction arrow and the
kernel inclusion in every degree. Localization preserves these equalities. -/
theorem supportComparisonSectionModel (k : Type u) [Field k] [IsAlgClosed k]
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    {C : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F) ⟶ J)
    (hh : QuasiIso h.hom) (hJ : ∀ n : ℤ, Injective (J.obj.X n))
    (ha : QuasiIso (supportComparisonAugmentation T A F J h))
    (hI : ∀ n : ℤ, Injective
      (((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj.X n))
    (θ : DerivedCategory.Plus.Q.obj
        ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J) ≅
      (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj
          (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F))))
    (hθ : θ.hom ≫ supportComparisonDerivedResolutionMap T A F J h =
      (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj J))
    (hunit : DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk (supportComparisonAugmentation T A F J h)) ≫ θ.hom =
      (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} A) T).unit.app
        (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F))) :
    ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) i.openComplement.ι).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) ≫
      (comparisonPullbackOpenUnitC A i.openComplement.ι).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) i.openComplement.toScheme).unit.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) i.openComplement.ι).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) i.openComplement.toScheme).map
          ((comparisonPullbackOpenUnitGamma A i.openComplement.ι).hom.app F)) ∧
    (sectionModelAugmentation i.openComplement.toScheme A
        (sectionModelOpenSource T A i (supportComparisonSource T A F))
        (sectionModelOpenResolution T A i J)
        (sectionModelOpenAugmentation T A i (supportComparisonSource T A F) J h) =
      (supportRestrictEt A i.openComplement).mapCochainComplexPlus.map
        (sectionModelAugmentation T A (supportComparisonSource T A F) J h)) ∧
    Nonempty (SupportSectionModelComputation T A (supportComparisonSource T A F) J h
      (supportEvalEt A T) (supportEvalPro A T) (supportEvaluationIdentity A T)
      ((sectionModelGlobalComparison T A).app
        (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F)))) ∧
    Nonempty (SupportSectionModelComputation i.openComplement.toScheme A
      (sectionModelOpenSource T A i (supportComparisonSource T A F))
      (sectionModelOpenResolution T A i J)
      (sectionModelOpenAugmentation T A i (supportComparisonSource T A F) J h)
      (supportEvalEt A i.openComplement.toScheme) (supportEvalPro A i.openComplement.toScheme)
      (supportEvaluationIdentity A i.openComplement.toScheme)
      ((sectionModelGlobalComparison i.openComplement.toScheme A).app
        (DerivedCategory.Plus.Q.obj
          (sectionModelOpenSource T A i (supportComparisonSource T A F))))) ∧
    Nonempty (SupportSectionModelComputation T A (supportComparisonSource T A F) J h
      (supportEt A i) (supportPro A i) (supportKernelIdentity A i)
      ((supportComparison A i).app
        (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F)))) ∧
    (∀ b : DerivedSupportDirectImageComparison A,
      (supportComparisonUnbounded A i
          (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F))) =
        (Functor.rightDerivedFunctorNatTrans (supportKernelEvaluationIso A i).hom).app
            (DerivedCategory.Q.obj (supportComparisonSource T A F).obj) ≫
          (supportEt A i).rightDerivedFunctor.map
            ((supportDerivedAdjunction A T).unit.app
              (DerivedCategory.Q.obj (supportComparisonSource T A F).obj)) ≫
          (b.b i).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
              (DerivedCategory.Q.obj (supportComparisonSource T A F).obj))) ∧
    (∀ n : ℤ,
      kernel.ι
          ((((comparisonLowerStar
              (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj.X n).obj.map
            (Etale.supportRestrictionArrow i).op) =
        kernel.ι ((J.obj.X n).obj.map (supportRestrictionArrow i).op)) ∧
    (∀ n : ℤ,
      ((((comparisonLowerStar
              (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj.X n).obj.map
            (Etale.supportRestrictionArrow i).op) =
        (J.obj.X n).obj.map (supportRestrictionArrow i).op) := by
  sorry

/-- Naturality of the normalized computations in maps of augmented resolutions.
This predicate just spells out the naturality clause of the section-model statement.
Source: Tag 09XP, functorial kernel restriction construction
(blueprint: lem-pur-support-comparison-section-model). -/
def SectionModelComputationsNatural
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A)
    (H : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A)
    [G.Additive] [H.Additive]
    (e : comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙ G ≅ H)
    (c : G.rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        H.rightDerivedFunctorPlus) : Prop :=
  ∀ (F F' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J J' : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F) ⟶ J)
    (h' : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F') ⟶ J')
    (f : (supportComparisonSource T A F) ⟶ (supportComparisonSource T A F')) (t : J ⟶ J'),
    QuasiIso h.hom → QuasiIso h'.hom →
    (∀ n : ℤ, Injective (J.obj.X n)) →
    (∀ n : ℤ, Injective (J'.obj.X n)) →
    QuasiIso (sectionModelAugmentation T A (supportComparisonSource T A F) J h).hom →
    QuasiIso (sectionModelAugmentation T A (supportComparisonSource T A F') J' h').hom →
    h ≫ t = (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.map f ≫ h' →
    ∀ (d : SupportSectionModelComputation T A (supportComparisonSource T A F) J h G H e
        (c.app (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F))))
      (d' : SupportSectionModelComputation T A (supportComparisonSource T A F') J' h' G H e
        (c.app (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F')))),
      sectionModelAugmentation T A (supportComparisonSource T A F) J h ≫
          (comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.map t =
        f ≫ sectionModelAugmentation T A (supportComparisonSource T A F') J' h' ∧
      DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map
          ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.map t)) ≫
          d'.et.hom =
        d.et.hom ≫ G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ∧
      DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map t) ≫ d'.pro.hom =
        d.pro.hom ≫ H.rightDerivedFunctorPlus.map
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.map
            (DerivedCategory.Plus.Q.map f)) ∧
      ((G.mapHomologicalComplex (.up ℤ)).map
          (((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex
            (.up ℤ)).map t.hom)) ≫
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app J'.obj) =
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app J.obj) ≫
          (H.mapHomologicalComplex (.up ℤ)).map t.hom

/-- Naturality of the open-complement computations, built from the restricted
augmented resolutions `j⁻¹(F[0])`, `j⁻¹J`, `h_V = j⁻¹h ∘ beta`, in maps of augmented
resolutions on `T`. This spells out the naturality clause of the section-model
statement for the identification on `V`.
Source: Tag 09XP, functorial kernel restriction construction
(blueprint: lem-pur-support-comparison-section-model). -/
def SectionModelOpenComputationsNatural {C : Scheme.{u}} (i : C ⟶ T)
    [IsClosedImmersion i] : Prop :=
  ∀ (F F' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J J' : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F) ⟶ J)
    (h' : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F') ⟶ J')
    (f : (supportComparisonSource T A F) ⟶ (supportComparisonSource T A F')) (t : J ⟶ J'),
    QuasiIso h.hom → QuasiIso h'.hom →
    (∀ n : ℤ, Injective (J.obj.X n)) →
    (∀ n : ℤ, Injective (J'.obj.X n)) →
    QuasiIso (sectionModelAugmentation T A (supportComparisonSource T A F) J h).hom →
    QuasiIso (sectionModelAugmentation T A (supportComparisonSource T A F') J' h').hom →
    h ≫ t = (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.map f ≫ h' →
    ∀ (d : SupportSectionModelComputation i.openComplement.toScheme A
        (sectionModelOpenSource T A i (supportComparisonSource T A F))
        (sectionModelOpenResolution T A i J)
        (sectionModelOpenAugmentation T A i (supportComparisonSource T A F) J h)
        (supportEvalEt A i.openComplement.toScheme)
        (supportEvalPro A i.openComplement.toScheme)
        (supportEvaluationIdentity A i.openComplement.toScheme)
        ((sectionModelGlobalComparison i.openComplement.toScheme A).app
          (DerivedCategory.Plus.Q.obj
            (sectionModelOpenSource T A i (supportComparisonSource T A F)))))
      (d' : SupportSectionModelComputation i.openComplement.toScheme A
        (sectionModelOpenSource T A i (supportComparisonSource T A F'))
        (sectionModelOpenResolution T A i J')
        (sectionModelOpenAugmentation T A i (supportComparisonSource T A F') J' h')
        (supportEvalEt A i.openComplement.toScheme)
        (supportEvalPro A i.openComplement.toScheme)
        (supportEvaluationIdentity A i.openComplement.toScheme)
        ((sectionModelGlobalComparison i.openComplement.toScheme A).app
          (DerivedCategory.Plus.Q.obj
            (sectionModelOpenSource T A i (supportComparisonSource T A F'))))),
      sectionModelAugmentation i.openComplement.toScheme A
          (sectionModelOpenSource T A i (supportComparisonSource T A F))
          (sectionModelOpenResolution T A i J)
          (sectionModelOpenAugmentation T A i (supportComparisonSource T A F) J h) ≫
          (comparisonLowerStar (ModuleCat.{u + 1} A)
            i.openComplement.toScheme).mapCochainComplexPlus.map
            ((supportRestrictPro A i.openComplement).mapCochainComplexPlus.map t) =
        (supportRestrictEt A i.openComplement).mapCochainComplexPlus.map f ≫
          sectionModelAugmentation i.openComplement.toScheme A
            (sectionModelOpenSource T A i (supportComparisonSource T A F'))
            (sectionModelOpenResolution T A i J')
            (sectionModelOpenAugmentation T A i (supportComparisonSource T A F') J' h') ∧
      DerivedCategory.Plus.Q.map
          ((supportEvalEt A i.openComplement.toScheme).mapCochainComplexPlus.map
            ((comparisonLowerStar (ModuleCat.{u + 1} A)
              i.openComplement.toScheme).mapCochainComplexPlus.map
              ((supportRestrictPro A i.openComplement).mapCochainComplexPlus.map t))) ≫
          d'.et.hom =
        d.et.hom ≫ (supportEvalEt A i.openComplement.toScheme).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((supportRestrictEt A i.openComplement).mapCochainComplexPlus.map f)) ∧
      DerivedCategory.Plus.Q.map
          ((supportEvalPro A i.openComplement.toScheme).mapCochainComplexPlus.map
            ((supportRestrictPro A i.openComplement).mapCochainComplexPlus.map t)) ≫
          d'.pro.hom =
        d.pro.hom ≫ (supportEvalPro A i.openComplement.toScheme).rightDerivedFunctorPlus.map
          ((comparisonUpperStar (ModuleCat.{u + 1} A)
            i.openComplement.toScheme).mapDerivedCategoryPlus.map
            (DerivedCategory.Plus.Q.map
              ((supportRestrictEt A i.openComplement).mapCochainComplexPlus.map f))) ∧
      ((supportEvalEt A i.openComplement.toScheme).mapHomologicalComplex (.up ℤ)).map
          (((comparisonLowerStar (ModuleCat.{u + 1} A)
            i.openComplement.toScheme).mapHomologicalComplex (.up ℤ)).map
            ((supportRestrictPro A i.openComplement).mapCochainComplexPlus.map t).hom) ≫
          ((NatTrans.mapHomologicalComplex
            (supportEvaluationIdentity A i.openComplement.toScheme).hom (.up ℤ)).app
            (sectionModelOpenResolution T A i J').obj) =
        ((NatTrans.mapHomologicalComplex
            (supportEvaluationIdentity A i.openComplement.toScheme).hom (.up ℤ)).app
            (sectionModelOpenResolution T A i J).obj) ≫
          ((supportEvalPro A i.openComplement.toScheme).mapHomologicalComplex (.up ℤ)).map
            ((supportRestrictPro A i.openComplement).mapCochainComplexPlus.map t).hom

/-- The normalized identifications commute with chain maps lifting sheaf morphisms,
for the whole space, its open complement (with the restricted augmentations), and
the support kernel.
Source: Tag 09XP, kernel restriction construction, node proof step 6
(blueprint: lem-pur-support-comparison-section-model).

Proof: for t h = h' nu*f, naturality of the ordinary unit gives
nu_*t a = a' f. Evaluation of nu_*t is literally evaluation of t. Naturality
of t commutes with restriction; the kernel universal property gives the same
identity on support kernels and preserves their inclusions. Localize these
identities. The canonical right-derived units are natural in chain maps, so
compose with the augmentation normalization equations and cancel the derived
images of the quasi-isomorphisms a and h. This gives the two displayed naturality
squares for the computation isomorphisms. On V, restrict t and f; naturality of
the canonical comparison beta and of restriction gives
(j⁻¹t) h_V = h'_V nu_V*(j⁻¹f), so the same argument applies to the restricted
augmentations a_V = j⁻¹a and h_V. This argument applies to the degree-zero
source complexes of sheaves, their open restrictions, and all chain maps lifting
the sheaf maps; it uses no assertion about connecting morphisms. -/
theorem supportComparisonSectionModel_naturality
    (k : Type u) [Field k] [IsAlgClosed k]
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    {C : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i] :
    SectionModelComputationsNatural T A
      (supportEvalEt A T) (supportEvalPro A T) (supportEvaluationIdentity A T)
      (sectionModelGlobalComparison T A) ∧
    SectionModelOpenComputationsNatural T A i ∧
    SectionModelComputationsNatural T A
      (supportEt A i) (supportPro A i) (supportKernelIdentity A i)
      (supportComparison A i) := by
  sorry

end AlgebraicGeometry.ProEtale
