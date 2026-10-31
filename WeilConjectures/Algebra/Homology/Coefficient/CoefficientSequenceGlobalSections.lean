/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.TowerRightDerivedEvaluation.TowerRightDerivedEvaluation
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Derived sections of strict coefficient sequences

Source: Stacks Project, Cohomology on Sites, Tags 0941 and 0D6E
(blueprint: lem-coef-sequence-global-sections-evaluation).
Natural number n denotes positive level n+1. All derived categories are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
-- These related localization proofs share large instance expressions.
-- Elaborating them serially avoids duplicating that work across proof tasks.
set_option Elab.async false

universe u v w a av b bv dA dD
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

section GenericLocalizedSquare

universe uc vc ud vd ue ve uf vf ug vg dc dd de df dg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localizedSquareTransition
    {C : Type uc} [Category.{vc} C] {D : Type ud} [Category.{vd} D]
    {E : Type ue} [Category.{ve} E] {F : Type uf} [Category.{vf} F]
    {G : Type ug} [Category.{vg} G]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F] [Abelian G]
    [HasDerivedCategory.{dc} C] [HasDerivedCategory.{dd} D] [HasDerivedCategory.{de} E]
    [HasDerivedCategory.{df} F] [HasDerivedCategory.{dg} G]
    (U : C ⥤ D) (an am : D ⥤ G) (en : C ⥤ E) (em : C ⥤ F)
    (b : F ⥤ E) (rn : E ⥤ G) (rm : F ⥤ G)
    [U.Additive] [an.Additive] [am.Additive] [en.Additive] [em.Additive]
    [b.Additive] [rn.Additive] [rm.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits an] [PreservesFiniteColimits an]
    [PreservesFiniteLimits am] [PreservesFiniteColimits am]
    [PreservesFiniteLimits en] [PreservesFiniteColimits en]
    [PreservesFiniteLimits em] [PreservesFiniteColimits em]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [PreservesFiniteLimits rn] [PreservesFiniteColimits rn]
    [PreservesFiniteLimits rm] [PreservesFiniteColimits rm]
    (c : b ⋙ rn ≅ rm) (enIso : U ⋙ an ≅ en ⋙ rn) (emIso : U ⋙ am ≅ em ⋙ rm)
    (t : an ⟶ am) (τ : en ⟶ em ⋙ b)
    (td : an.mapDerivedCategory ⟶ am.mapDerivedCategory)
    (τd : en.mapDerivedCategory ⟶ em.mapDerivedCategory ⋙ b.mapDerivedCategory)
    (dn : U.mapDerivedCategory ⋙ an.mapDerivedCategory ⟶
      en.mapDerivedCategory ⋙ rn.mapDerivedCategory)
    (dm : U.mapDerivedCategory ⋙ am.mapDerivedCategory ⟶
      em.mapDerivedCategory ⋙ rm.mapDerivedCategory)
    (hdn : ∀ K : CochainComplex C ℤ,
      dn.app (DerivedCategory.Q.obj K) ≫
        rn.mapDerivedCategory.map (en.mapDerivedCategoryFactors.hom.app K) ≫
        rn.mapDerivedCategoryFactors.hom.app ((en.mapHomologicalComplex (.up ℤ)).obj K) =
      an.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        an.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex enIso.hom (.up ℤ)).app K))
    (hdm : ∀ K : CochainComplex C ℤ,
      dm.app (DerivedCategory.Q.obj K) ≫
        rm.mapDerivedCategory.map (em.mapDerivedCategoryFactors.hom.app K) ≫
        rm.mapDerivedCategoryFactors.hom.app ((em.mapHomologicalComplex (.up ℤ)).obj K) =
      am.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        am.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex emIso.hom (.up ℤ)).app K))
    (htd : ∀ K : CochainComplex D ℤ,
      td.app (DerivedCategory.Q.obj K) ≫ am.mapDerivedCategoryFactors.hom.app K =
        an.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K))
    (hτd : ∀ K : CochainComplex C ℤ,
      τd.app (DerivedCategory.Q.obj K) ≫
        b.mapDerivedCategory.map (em.mapDerivedCategoryFactors.hom.app K) ≫
        b.mapDerivedCategoryFactors.hom.app ((em.mapHomologicalComplex (.up ℤ)).obj K) =
      en.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))
    (h : Functor.whiskerLeft U t ≫ emIso.hom =
      enIso.hom ≫ Functor.whiskerRight τ rn ≫ Functor.whiskerLeft em c.hom) :
    Functor.whiskerLeft U.mapDerivedCategory td ≫ dm =
      dn ≫ Functor.whiskerRight τd rn.mapDerivedCategory ≫
        Functor.whiskerLeft em.mapDerivedCategory
          (Functor.exactDerivedRestrictionComposition b rn rm c).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  let UK := (U.mapHomologicalComplex (.up ℤ)).obj K
  let cd := Functor.exactDerivedRestrictionComposition b rn rm c
  change td.app (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      dm.app (DerivedCategory.Q.obj K) = dn.app (DerivedCategory.Q.obj K) ≫
        rn.mapDerivedCategory.map (τd.app (DerivedCategory.Q.obj K)) ≫
          cd.hom.app (em.mapDerivedCategory.obj (DerivedCategory.Q.obj K))
  apply (cancel_mono (rm.mapDerivedCategory.map (em.mapDerivedCategoryFactors.hom.app K) ≫
      rm.mapDerivedCategoryFactors.hom.app ((em.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simp only [Category.assoc]
  rw [hdm K]
  erw [← Category.assoc, ← td.naturality, Category.assoc]
  erw [← Category.assoc (td.app _) _ _, htd UK]
  simp only [Category.assoc]
  have hc := cd.hom.naturality (em.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hc
  have hcf := Functor.exactDerivedRestrictionComposition_hom_factors b rn rm c
    ((em.mapHomologicalComplex (.up ℤ)).obj K)
  erw [← Category.assoc (cd.hom.app _) _ _, ← hc]
  erw [Category.assoc (rn.mapDerivedCategory.map
    (b.mapDerivedCategory.map (em.mapDerivedCategoryFactors.hom.app K))) _ _, hcf]
  simp only [← rn.mapDerivedCategory.map_comp_assoc]
  erw [hτd K, rn.mapDerivedCategory.map_comp]
  have hn := rn.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc (rn.mapDerivedCategory.map (en.mapDerivedCategoryFactors.hom.app K)) _ _]
  have hn' := congrArg (fun q ↦ q ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
      ((em.mapHomologicalComplex (.up ℤ)).obj K))) hn
  simp only [Category.assoc] at hn'
  erw [hn']
  have he := congrArg (fun q ↦ q ≫ DerivedCategory.Q.map
      ((rn.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))) (hdn K)
  have he' := congrArg (fun q ↦ q ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
      ((em.mapHomologicalComplex (.up ℤ)).obj K))) he
  simp only [Category.assoc] at he'
  erw [he']
  simp only [← DerivedCategory.Q.map_comp]
  congr 2
  apply congrArg DerivedCategory.Q.map
  have ho := congrArg (fun q ↦ (NatTrans.mapHomologicalComplex q (.up ℤ)).app K) h
  simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] at ho
  exact ho

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem canonicalSquareTransition
    {C : Type uc} [Category.{vc} C] {D : Type ud} [Category.{vd} D]
    {E : Type ue} [Category.{ve} E] {F : Type uf} [Category.{vf} F]
    {G : Type ug} [Category.{vg} G]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F] [Abelian G]
    [HasDerivedCategory.{dc} C] [HasDerivedCategory.{dd} D] [HasDerivedCategory.{de} E]
    [HasDerivedCategory.{df} F] [HasDerivedCategory.{dg} G]
    (U : C ⥤ D) (an am : D ⥤ G) (en : C ⥤ E) (em : C ⥤ F)
    (b : F ⥤ E) (rn : E ⥤ G) (rm : F ⥤ G)
    [U.Additive] [an.Additive] [am.Additive] [en.Additive] [em.Additive]
    [b.Additive] [rn.Additive] [rm.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits an] [PreservesFiniteColimits an]
    [PreservesFiniteLimits am] [PreservesFiniteColimits am]
    [PreservesFiniteLimits en] [PreservesFiniteColimits en]
    [PreservesFiniteLimits em] [PreservesFiniteColimits em]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [PreservesFiniteLimits rn] [PreservesFiniteColimits rn]
    [PreservesFiniteLimits rm] [PreservesFiniteColimits rm]
    (c : b ⋙ rn ≅ rm) (enIso : U ⋙ an ≅ en ⋙ rn) (emIso : U ⋙ am ≅ em ⋙ rm)
    (t : an ⟶ am) (τ : en ⟶ em ⋙ b)
    (td : an.mapDerivedCategory ⟶ am.mapDerivedCategory)
    (τd : en.mapDerivedCategory ⟶ em.mapDerivedCategory ⋙ b.mapDerivedCategory)
    (htd : ∀ K : CochainComplex D ℤ,
      td.app (DerivedCategory.Q.obj K) ≫ am.mapDerivedCategoryFactors.hom.app K =
        an.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K))
    (hτd : ∀ K : CochainComplex C ℤ,
      τd.app (DerivedCategory.Q.obj K) ≫
        b.mapDerivedCategory.map (em.mapDerivedCategoryFactors.hom.app K) ≫
        b.mapDerivedCategoryFactors.hom.app ((em.mapHomologicalComplex (.up ℤ)).obj K) =
      en.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))
    (h : Functor.whiskerLeft U t ≫ emIso.hom =
      enIso.hom ≫ Functor.whiskerRight τ rn ≫ Functor.whiskerLeft em c.hom) :
    Functor.whiskerLeft U.mapDerivedCategory td ≫
        (Functor.mapDerivedCategorySquareIso emIso).hom =
      (Functor.mapDerivedCategorySquareIso enIso).hom ≫
        Functor.whiskerRight τd rn.mapDerivedCategory ≫
        Functor.whiskerLeft em.mapDerivedCategory
          (Functor.exactDerivedRestrictionComposition b rn rm c).hom := by
  exact localizedSquareTransition U an am en em b rn rm c enIso emIso t τ td τd
    (Functor.mapDerivedCategorySquareIso enIso).hom
    (Functor.mapDerivedCategorySquareIso emIso).hom
    (Functor.exactSquare_fac enIso) (Functor.exactSquare_fac emIso)
    htd hτd h

end GenericLocalizedSquare



variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The recorded module category at one coefficient ring.
Source: Stacks 03DA (blueprint: lem-coef-sequence-global-sections-evaluation). -/
abbrev sequenceCoefficientModules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)

/-- Actual scalar restriction at one coefficient map.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
abbrev sequenceCoefficientRestriction {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) :=
  restrictScalars.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f)

/-- Limits indexed by the essentially small site exist in the coefficient universe.
Source: Stacks 01FT (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceAbSiteLimits : HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w} :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Global sections are the limit of the underlying abelian presheaf, including maps.
Source: Stacks 01FT (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def sequenceCoefficientSections (R : Sheaf J CommRingCat.{w}) :
    sequenceCoefficientModules R ⥤ AddCommGrpCat.{w} :=
  toSheaf (derivedChangeRingIndependentCoefficients J R) ⋙
    sheafToPresheaf J AddCommGrpCat.{w} ⋙ lim

/-- Global sections preserve addition, as a finite-product-preserving functor.
Source: Stacks 01FT (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceCoefficientSectionsAdditive (R : Sheaf J CommRingCat.{w}) :
    (sequenceCoefficientSections R).Additive :=
  by
    dsimp only [sequenceCoefficientSections]
    exact Functor.additive_of_preserves_binary_products _

/-- Termwise global sections retain every actual tower arrow.
Source: Stacks 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def sequenceTowerSections (A : Sheaf J CommRingCat.{w}) :
    (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (Functor.whiskeringRight _ _ _).obj (sequenceCoefficientSections A)

/-- Standard localization for constant-coefficient towers.
Source: Stacks 05RU (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceConstantTowerHasDerived (A : Sheaf J CommRingCat.{w}) :
    HasDerivedCategory (ℕᵒᵖ ⥤ sequenceCoefficientModules A) :=
  HasDerivedCategory.standard _

/-- Standard localization for the abelian target.
Source: Stacks 05RU (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceAbHasDerived : HasDerivedCategory AddCommGrpCat.{w} :=
  HasDerivedCategory.standard _

/-- Standard localization for the strict abelian tower target.
Source: Stacks 05RU (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceAbTowerHasDerived : HasDerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  HasDerivedCategory.standard _

/-- A total right derived pair, with its universal unit and K-injective computation.
Source: Stacks 070I, 070Y (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceSectionsDerivedPair
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{dA} A]
    {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{dD} D]
    (F : A ⥤ D) [F.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory D
  unit : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)

section Generic

universe da db sep
variable {E : Type a} [Category.{av} E] [Abelian E] [HasDerivedCategory.{da} E]
  {F : Type b} [Category.{bv} F] [Abelian F] [HasDerivedCategory.{db} F]

omit [HasDerivedCategory E] in
private theorem sectionsDerives (T : E ⥤ F) [T.Additive] :
    (CochainComplex.KInjectives.localizerMorphism E).Derives
      (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : X.obj.IsKInjective := X.property
  have : Y.obj.IsKInjective := Y.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (T.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

private theorem sectionsPairExists [Abelian.HasKInjectiveResolutions E]
    (T : E ⥤ F) [T.Additive] : Nonempty (SequenceSectionsDerivedPair T) := by
  let G := T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let W := HomologicalComplex.quasiIso E (.up ℤ)
  have h := sectionsDerives T
  have := h.hasPointwiseRightDerivedFunctor
  refine ⟨⟨G.totalRightDerived DerivedCategory.Q W,
    G.totalRightDerivedUnit DerivedCategory.Q W, inferInstance, ?_⟩⟩
  intro I hI
  exact h.isIso_of_isRightDerivedFunctor _ (CochainComplex.KInjectives.mk I)

omit [HasDerivedCategory E] in
private theorem sectionsTowerGrothendieck
    [IsGrothendieckAbelian.{sep} E] : IsGrothendieckAbelian.{sep} (ℕᵒᵖ ⥤ E) := by
  let G := separator E
  have hG := isSeparator_separator E
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint E n).obj G) := by
    intro M N f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight E n
    apply (adj.homEquiv G N).symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G M).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ E) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{sep, sep} (ℕᵒᵖ ⥤ E) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{sep, sep} (ℕᵒᵖ ⥤ E) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun M N ↦ small_of_injective
    (f := fun f : M ⟶ N ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

end Generic

private theorem scalarComparisonExists [HasDerivedCategory AddCommGrpCat.{w}]
    {E : Type a} [Category.{av} E] [Abelian E] [HasDerivedCategory.{dA} E]
    {F : Type b} [Category.{bv} F] [Abelian F] [HasDerivedCategory.{dD} F]
    [Abelian.HasKInjectiveResolutions F]
    (r : F ⥤ E) [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (G : E ⥤ AddCommGrpCat.{w}) [G.Additive]
    (GS : F ⥤ AddCommGrpCat.{w}) [GS.Additive]
    (P : SequenceSectionsDerivedPair G) (S : SequenceSectionsDerivedPair GS)
    (hGS : GS = r ⋙ G)
    (hC : ∀ (I : CochainComplex F ℤ), I.IsKInjective →
      IsIso (P.unit.app ((r.mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃ e : S.functor ≅ r.mapDerivedCategory ⋙ P.functor,
      ∀ K : CochainComplex F ℤ,
        HEq (S.unit.app K ≫ e.hom.app (DerivedCategory.Q.obj K))
          (P.unit.app ((r.mapHomologicalComplex (.up ℤ)).obj K) ≫
            P.functor.map (r.mapDerivedCategoryFactors.inv.app K)) := by
  subst GS
  let η : (r ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ r.mapDerivedCategory ⋙ P.functor :=
    Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) P.unit ≫
      Functor.whiskerRight r.mapDerivedCategoryFactors.inv P.functor
  obtain ⟨e, he⟩ := TowerRightDerivedEvaluation.descend_comparison
    (fun K ↦ by
      obtain ⟨I, hI, a, ha, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
      exact ⟨I, a, hI, hq⟩)
    S.functor (r.mapDerivedCategory ⋙ P.functor) _ S.unit η S.computes
    (fun I hI ↦ by
      have := hC I hI
      change IsIso (P.unit.app _ ≫ P.functor.map (r.mapDerivedCategoryFactors.inv.app I))
      infer_instance)
  refine ⟨e, fun K ↦ heq_of_eq ?_⟩
  exact he K

private theorem composition_normalization
    {D : Type*} [Category D]
    {A B C E F G H I L : D}
    (u : A ⟶ B) (v : A ⟶ C) (w : A ⟶ E) (z : A ⟶ F)
    (s : B ⟶ G) (t : C ⟶ H) (t' : G ⟶ I) (k : B ⟶ L)
    (a : C ⟶ G) (b : E ⟶ H) (c : H ⟶ I) (d : I ⟶ L)
    (e : E ⟶ F) (f : F ⟶ L)
    (hs : u ≫ s = v ≫ a) (ht : v ≫ t = w ≫ b)
    (hn : a ≫ t' = t ≫ c) (hcomp : b ≫ c ≫ d = e ≫ f)
    (hu : w ≫ e = z) (hk : u ≫ k = z ≫ f) :
    u ≫ s ≫ t' ≫ d = u ≫ k := by
  calc
    u ≫ s ≫ t' ≫ d = (u ≫ s) ≫ t' ≫ d := by simp only [Category.assoc]
    _ = (v ≫ a) ≫ t' ≫ d := by rw [hs]
    _ = v ≫ (a ≫ t') ≫ d := by simp only [Category.assoc]
    _ = v ≫ (t ≫ c) ≫ d := by rw [hn]
    _ = (v ≫ t) ≫ c ≫ d := by simp only [Category.assoc]
    _ = (w ≫ b) ≫ c ≫ d := by rw [ht]
    _ = w ≫ (b ≫ c ≫ d) := by simp only [Category.assoc]
    _ = w ≫ (e ≫ f) := by rw [hcomp]
    _ = z ≫ f := by rw [← Category.assoc, hu]
    _ = u ≫ k := hk.symm

section GenericScalar

universe c cv dc

private theorem derivedScalarCocycle [HasDerivedCategory AddCommGrpCat.{w}]
    {E : Type a} [Category.{av} E] [Abelian E] [HasDerivedCategory.{dA} E]
    {F : Type b} [Category.{bv} F] [Abelian F] [HasDerivedCategory.{dD} F]
    {H : Type c} [Category.{cv} H] [Abelian H] [HasDerivedCategory.{dc} H]
    (rg : H ⥤ F) (rf : F ⥤ E) (rk : H ⥤ E)
    [rg.Additive] [rf.Additive] [rk.Additive]
    [PreservesFiniteLimits rg] [PreservesFiniteColimits rg]
    [PreservesFiniteLimits rf] [PreservesFiniteColimits rf]
    [PreservesFiniteLimits rk] [PreservesFiniteColimits rk]
    (G : E ⥤ AddCommGrpCat.{w}) [G.Additive]
    (P : SequenceSectionsDerivedPair G)
    (GS : F ⥤ AddCommGrpCat.{w}) [GS.Additive]
    (GT : H ⥤ AddCommGrpCat.{w}) [GT.Additive]
    (S : SequenceSectionsDerivedPair GS) (T : SequenceSectionsDerivedPair GT)
    (hGS : GS = rf ⋙ G) (hGT : GT = rg ⋙ rf ⋙ G)
    (sf : S.functor ≅ rf.mapDerivedCategory ⋙ P.functor)
    (sg : T.functor ≅ rg.mapDerivedCategory ⋙ S.functor)
    (sk : T.functor ≅ rk.mapDerivedCategory ⋙ P.functor)
    (c : rg ⋙ rf ≅ rk)
    (hf : ∀ L : CochainComplex F ℤ,
      HEq (S.unit.app L ≫ sf.hom.app (DerivedCategory.Q.obj L))
        (P.unit.app ((rf.mapHomologicalComplex (.up ℤ)).obj L) ≫
          P.functor.map (rf.mapDerivedCategoryFactors.inv.app L)))
    (hg : ∀ K : CochainComplex H ℤ,
      HEq (T.unit.app K ≫ sg.hom.app (DerivedCategory.Q.obj K))
        (S.unit.app ((rg.mapHomologicalComplex (.up ℤ)).obj K) ≫
          S.functor.map (rg.mapDerivedCategoryFactors.inv.app K)))
    (hk : ∀ K : CochainComplex H ℤ,
      HEq (T.unit.app K ≫ sk.hom.app (DerivedCategory.Q.obj K))
        (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K)) ≫
          P.unit.app ((rk.mapHomologicalComplex (.up ℤ)).obj K) ≫
          P.functor.map (rk.mapDerivedCategoryFactors.inv.app K))) :
    sg.hom ≫ Functor.whiskerLeft rg.mapDerivedCategory sf.hom ≫
        Functor.whiskerRight
          (Functor.exactDerivedRestrictionComposition rg rf rk c).hom P.functor = sk.hom := by
  subst GS
  subst GT
  have := T.universal
  apply Functor.rightDerived_ext T.functor T.unit (HomologicalComplex.quasiIso H (.up ℤ))
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let L := (rg.mapHomologicalComplex (.up ℤ)).obj K
  let LL := (rf.mapHomologicalComplex (.up ℤ)).obj L
  let LK := (rk.mapHomologicalComplex (.up ℤ)).obj K
  let cd := Functor.exactDerivedRestrictionComposition rg rf rk c
  let ec := (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K
  let z := DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map ec) ≫ P.unit.app LK
  refine composition_normalization
    (T.unit.app K) (S.unit.app L) (P.unit.app LL) z
    (sg.hom.app (DerivedCategory.Q.obj K)) (sf.hom.app (DerivedCategory.Q.obj L))
    (sf.hom.app (rg.mapDerivedCategory.obj (DerivedCategory.Q.obj K)))
    (sk.hom.app (DerivedCategory.Q.obj K))
    (S.functor.map (rg.mapDerivedCategoryFactors.inv.app K))
    (P.functor.map (rf.mapDerivedCategoryFactors.inv.app L))
    (P.functor.map (rf.mapDerivedCategory.map (rg.mapDerivedCategoryFactors.inv.app K)))
    (P.functor.map (cd.hom.app (DerivedCategory.Q.obj K)))
    (P.functor.map (DerivedCategory.Q.map ec))
    (P.functor.map (rk.mapDerivedCategoryFactors.inv.app K)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact eq_of_heq (hg K)
  · exact eq_of_heq (hf L)
  · exact sf.hom.naturality (rg.mapDerivedCategoryFactors.inv.app K)
  · have hc := congrArg P.functor.map
      (Functor.exactDerivedRestrictionComposition_inv_factors rg rf rk c K)
    dsimp only [LL, L, cd, ec, Functor.comp_obj]
    have hm := P.functor.map_comp (DerivedCategory.Q.map ec)
      (rk.mapDerivedCategoryFactors.inv.app K)
    have hc' := hc.trans hm
    dsimp only [ec, Functor.comp_obj] at hc'
    simp only [P.functor.map_comp] at hc'
    exact hc'
  · exact (P.unit.naturality ec).symm
  · dsimp only [z, LK, ec]
    erw [Category.assoc]
    exact eq_of_heq (hk K)

end GenericScalar

/-- The exact termwise restriction, specified on objects, maps and all transitions.
These equations determine the functor, rather than supplying an arbitrary exact map.
Source: Stacks 03CZ, 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceCoefficientRestrictionData
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) where
  functor : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ sequenceCoefficientModules A)
  additive : functor.Additive
  limits : PreservesFiniteLimits functor
  colimits : PreservesFiniteColimits functor
  evaluation : ∀ n : ℕ, functor ⋙ (CategoryTheory.evaluation ℕᵒᵖ _).obj (op n) ≅
    systemEvaluation B n ⋙ sequenceCoefficientRestriction (α.app (op n))
  evaluation_sections : ∀ (n : ℕ) (M : StrictRingSystem B) (V : Cᵒᵖ)
    (x : ((functor.obj M).obj (op n)).val.obj V),
    HEq (((evaluation n).hom.app M).val.app V x) x
  transitions : ∀ (M : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (V : Cᵒᵖ)
    (x : ((functor.obj M).obj (op n)).val.obj V),
    HEq (((evaluation m).hom.app M).val.app V
      (((functor.obj M).map (homOfLE h).op).val.app V x))
      ((M.transition h).val.app V (((evaluation n).hom.app M).val.app V x))

/-- The given exact restriction has its specified additive structure.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceRestrictionAdditive
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α) :
    r.functor.Additive := r.additive

/-- The given restriction preserves finite limits.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceRestrictionLimits
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α) :
    PreservesFiniteLimits r.functor := r.limits

/-- The given restriction preserves finite colimits.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceRestrictionColimits
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α) :
    PreservesFiniteColimits r.functor := r.colimits

/-- Termwise sections preserve addition.
Source: Stacks 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceTowerSectionsAdditive (A : Sheaf J CommRingCat.{w}) :
    (sequenceTowerSections A).Additive := by
  dsimp only [sequenceTowerSections]
  infer_instance

/-- The evaluation comparison for exact restriction is its localized ordinary comparison.
Source: Stacks 015F (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def sequenceRestrictionDerivedEvaluation
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α)
    (n : ℕ) :
    r.functor.mapDerivedCategory ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategory ≅
      derivedSystemEvaluation B n ⋙
        (sequenceCoefficientRestriction (α.app (op n))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso r.functor
    ((CategoryTheory.evaluation ℕᵒᵖ _).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (r.evaluation n) ≪≫
    Functor.mapDerivedCategoryCompIso (systemEvaluation B n)
      (sequenceCoefficientRestriction (α.app (op n)))

/-- The two finite comparisons, with the actual total derived functors as their endpoints.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceSectionsComparisons
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) where
  restriction : SequenceCoefficientRestrictionData B A α
  finite : ∀ R : Sheaf J CommRingCat.{w},
    SequenceSectionsDerivedPair (sequenceCoefficientSections R)
  tower : SequenceSectionsDerivedPair (sequenceTowerSections A)
  evaluation : ∀ n : ℕ, tower.functor ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory ≅
    ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
      (op n)).mapDerivedCategory ⋙ (finite A).functor
  scalar : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S),
    (finite S).functor ≅
      (sequenceCoefficientRestriction f).mapDerivedCategory ⋙ (finite R).functor

/-- G is a composite of actual functors on ordinary derived categories.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def SequenceSectionsComparisons.global
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    DerivedCategory (StrictRingSystem B) ⥤ DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  d.restriction.functor.mapDerivedCategory ⋙ d.tower.functor

/-- The first comparison: restrict scalars exactly, then evaluate the same tower resolution.
Source: Stacks 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def SequenceSectionsComparisons.restrictedEvaluation
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) (n : ℕ) :
    d.global ⋙ ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
        (op n)).mapDerivedCategory ≅
      derivedSystemEvaluation B n ⋙
        (sequenceCoefficientRestriction (α.app (op n))).mapDerivedCategory ⋙
          (d.finite A).functor :=
  Functor.isoWhiskerLeft d.restriction.functor.mapDerivedCategory (d.evaluation n) ≪≫
    Functor.isoWhiskerRight (sequenceRestrictionDerivedEvaluation d.restriction n)
      (d.finite A).functor

/-- The second comparison is the inverse of the normalized scalar composition comparison.
Source: Stacks 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def SequenceSectionsComparisons.finiteEvaluation
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) (n : ℕ) :
    d.global ⋙ ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
        (op n)).mapDerivedCategory ≅
      derivedSystemEvaluation B n ⋙ (d.finite (B.obj (op n))).functor :=
  d.restrictedEvaluation n ≪≫
    Functor.isoWhiskerLeft (derivedSystemEvaluation B n) (d.scalar (α.app (op n))).symm

/-- Normalization by derived units and compatibility with every actual transition.
No condition on K-injectivity of varying-coefficient evaluations occurs here.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceSectionsComparisons.Normalized
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) : Prop where
  /-- The first comparison evaluates precisely the unit on the same K-injective tower. -/
  evaluation_unit : ∀ (n : ℕ)
    (I : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ), I.IsKInjective →
    ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategoryFactors.inv.app
        (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj I) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory.map
        (d.tower.unit.app I) ≫
      (d.evaluation n).hom.app (DerivedCategory.Q.obj I) ≫
      (d.finite A).functor.map
        (((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app I) =
      (d.finite A).unit.app
        ((((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj I)
  /-- The second comparison is the canonical derived direct-image composition map. -/
  scalar_unit : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
    (K : CochainComplex (sequenceCoefficientModules S) ℤ),
    (d.finite S).unit.app K ≫ (d.scalar f).hom.app (DerivedCategory.Q.obj K) ≫
      (d.finite R).functor.map
        ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.hom.app K) =
    (d.finite R).unit.app
      (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj K)
  /-- The evaluated tower comparison commutes with all constant-coefficient transitions. -/
  evaluation_transition : ∀ {m n : ℕ} (h : m ≤ n)
    (M : DerivedCategory (ℕᵒᵖ ⥤ sequenceCoefficientModules A)),
    (towerDerivedEvaluationTransition AddCommGrpCat.{w} (homOfLE h).op).app
        (d.tower.functor.obj M) ≫ (d.evaluation m).hom.app M =
      (d.evaluation n).hom.app M ≫ (d.finite A).functor.map
        ((towerDerivedEvaluationTransition (sequenceCoefficientModules A)
          (homOfLE h).op).app M)
  /-- Under both comparisons, the actual strict tower arrow is the derived-sections arrow
  of the original semilinear transition, followed by inverse scalar composition. -/
  finite_transition : ∀ {m n : ℕ} (h : m ≤ n) (M : DerivedCategory (StrictRingSystem B)),
    (towerDerivedEvaluationTransition AddCommGrpCat.{w} (homOfLE h).op).app
        (d.global.obj M) ≫ (d.finiteEvaluation m).hom.app M =
      (d.finiteEvaluation n).hom.app M ≫
        (d.finite (B.obj (op n))).functor.map ((systemDerivedTransition B h).app M) ≫
        (d.scalar (B.map (homOfLE h).op)).inv.app ((derivedSystemEvaluation B m).obj M)

-- Keep localization constructions behind their factorization API in the proof.
attribute [local irreducible] Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def coefficientRestrictionTower
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) (M : StrictRingSystem B) :
    ℕᵒᵖ ⥤ sequenceCoefficientModules A where
  obj n := (sequenceCoefficientRestriction (α.app n)).obj (M.level n.unop)
  map {n m} f :=
    (sequenceCoefficientRestriction (α.app n)).map (M.transition (leOfHom f.unop)) ≫
      (systemScalarRestrictionComposition (α.app n) (B.map f) (α.app m)
        (by simpa using α.naturality f)).hom.app (M.level m.unop)
  map_id n := by
    ext U x
    exact M.identity n.unop U x
  map_comp {n m l} f g := by
    ext U x
    exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x

private def coefficientRestrictionFunctor
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) :
    StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ sequenceCoefficientModules A) where
  obj := coefficientRestrictionTower B A α
  map {M N} f :=
    { app := fun n ↦ (sequenceCoefficientRestriction (α.app n)).map (f.app n.unop)
      naturality := by
        intro n m g
        ext U x
        exact congrArg (fun k ↦ k.val.app U x) (f.comm (leOfHom g.unop)).symm }

private def coefficientRestrictionEvaluation
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) (n : ℕ) :
    coefficientRestrictionFunctor B A α ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj (op n) ≅
      systemEvaluation B n ⋙ sequenceCoefficientRestriction (α.app (op n)) :=
  Iso.refl _

omit [EssentiallySmall.{w} C] in
private theorem coefficientRestriction_exact
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) :
    PreservesFiniteLimits (coefficientRestrictionFunctor B A α) ∧
      PreservesFiniteColimits (coefficientRestrictionFunctor B A α) := by
  constructor
  · constructor
    intro K _ _
    apply preservesLimitsOfShape_of_evaluation
    intro n
    change PreservesLimitsOfShape K
      (systemEvaluation B n.unop ⋙ sequenceCoefficientRestriction (α.app n))
    infer_instance
  · constructor
    intro K _ _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    change PreservesColimitsOfShape K
      (systemEvaluation B n.unop ⋙ sequenceCoefficientRestriction (α.app n))
    infer_instance

private def coefficientRestrictionData
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) : SequenceCoefficientRestrictionData B A α where
  functor := coefficientRestrictionFunctor B A α
  additive := by
    refine { map_add := ?_ }
    intro M N f g
    apply NatTrans.ext
    funext n
    change (sequenceCoefficientRestriction (α.app n)).map
        ((systemEvaluation B n.unop).map (f + g)) = _
    rw [Functor.map_add, Functor.map_add]
    rfl
  limits := (coefficientRestriction_exact B A α).1
  colimits := (coefficientRestriction_exact B A α).2
  evaluation := coefficientRestrictionEvaluation B A α
  evaluation_sections := by intros; rfl
  transitions := by intros; rfl

attribute [irreducible] coefficientRestrictionTower coefficientRestrictionFunctor
  coefficientRestrictionEvaluation coefficientRestrictionData

section GenericTower

universe dtA dtD

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientTowerComparison
    {E : Type a} [Category.{av} E] [Abelian E] [HasDerivedCategory.{dA} E]
    {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{dD} D]
    [HasDerivedCategory.{dtA} (ℕᵒᵖ ⥤ E)] [HasDerivedCategory.{dtD} (ℕᵒᵖ ⥤ D)]
    (S : E ⥤ D) [S.Additive]
    (P : SequenceSectionsDerivedPair S)
    (T : SequenceSectionsDerivedPair (((Functor.whiskeringRight ℕᵒᵖ E D).obj S)))
    (enoughT : ∀ K : CochainComplex (ℕᵒᵖ ⥤ E) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) (a : K ⟶ I),
        I.IsKInjective ∧ QuasiIso a) :
    ∃ β : ∀ n : ℕᵒᵖ, T.functor ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ D).obj n).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ E).obj n).mapDerivedCategory ⋙
        P.functor,
      (∀ (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ E) ℤ),
        ((CategoryTheory.evaluation ℕᵒᵖ D).obj n).mapDerivedCategoryFactors.inv.app
            (((((Functor.whiskeringRight ℕᵒᵖ E D).obj S)).mapHomologicalComplex (.up ℤ)).obj I) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ D).obj n).mapDerivedCategory.map
            (T.unit.app I) ≫
          (β n).hom.app (DerivedCategory.Q.obj I) ≫ P.functor.map
            (((CategoryTheory.evaluation ℕᵒᵖ E).obj
              n).mapDerivedCategoryFactors.hom.app I) =
        P.unit.app ((((CategoryTheory.evaluation ℕᵒᵖ E).obj
          n).mapHomologicalComplex (.up ℤ)).obj I)) ∧
      (∀ (m n : ℕᵒᵖ) (t : m ⟶ n)
        (M : DerivedCategory (ℕᵒᵖ ⥤ E)),
        (towerDerivedEvaluationTransition D t).app (T.functor.obj M) ≫
            (β n).hom.app M =
          (β m).hom.app M ≫ P.functor.map
            ((towerDerivedEvaluationTransition E t).app M)) := by
  classical
  let FT := (Functor.whiskeringRight ℕᵒᵖ E D).obj S
  let R := P.functor
  let RT := T.functor
  let η := P.unit
  let ηT := T.unit
  let FTc := FT.mapHomologicalComplex (.up ℤ)
  let EA (n : ℕᵒᵖ) := (CategoryTheory.evaluation ℕᵒᵖ E).obj n
  let EB (n : ℕᵒᵖ) := (CategoryTheory.evaluation ℕᵒᵖ D).obj n
  let a (n : ℕᵒᵖ) : FTc ⋙ (EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RT ⋙ (EB n).mapDerivedCategory :=
    Functor.whiskerLeft FTc (EB n).mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight ηT (EB n).mapDerivedCategory
  let b (n : ℕᵒᵖ) : FTc ⋙ (EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (EA n).mapDerivedCategory ⋙ R :=
    Functor.whiskerLeft ((EA n).mapHomologicalComplex (.up ℤ)) η ≫
      Functor.whiskerRight (EA n).mapDerivedCategoryFactors.inv R
  have ha (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ E) ℤ)
      (hI : I.IsKInjective) : IsIso ((a n).app I) := by
    have := T.computes I hI
    change IsIso ((EB n).mapDerivedCategoryFactors.inv.app (FTc.obj I) ≫
      (EB n).mapDerivedCategory.map (T.unit.app I))
    infer_instance
  have hb (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ E) ℤ)
      (hI : I.IsKInjective) : IsIso ((b n).app I) := by
    have hE := tower_evaluation_isKInjective (E) I n
    have := P.computes (((EA n).mapHomologicalComplex (.up ℤ)).obj I) hE
    change IsIso (P.unit.app (((EA n).mapHomologicalComplex (.up ℤ)).obj I) ≫
      R.map ((EA n).mapDerivedCategoryFactors.inv.app I))
    infer_instance
  have ex (n : ℕᵒᵖ) := TowerRightDerivedEvaluation.descend_comparison enoughT
    (RT ⋙ (EB n).mapDerivedCategory) ((EA n).mapDerivedCategory ⋙ R)
    _ (a n) (b n) (ha n) (hb n)
  choose β hβ using ex
  have hn (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) :
      (EB n).mapDerivedCategoryFactors.inv.app (FTc.obj I) ≫
        (EB n).mapDerivedCategory.map (T.unit.app I) ≫
        (β n).hom.app (DerivedCategory.Q.obj I) ≫
        R.map ((EA n).mapDerivedCategoryFactors.hom.app I) =
      P.unit.app (((EA n).mapHomologicalComplex (.up ℤ)).obj I) := by
    have h := congrArg
      (fun f ↦ f ≫ R.map ((EA n).mapDerivedCategoryFactors.hom.app I)) (hβ n I)
    dsimp only [a, b, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app] at h
    simp only [Category.assoc, ← R.map_comp, Iso.inv_hom_id_app, R.map_id] at h
    erw [Category.comp_id] at h
    exact h
  refine ⟨β, hn, ?_⟩
  intro m n t M
  let sA := towerDerivedEvaluationTransition E t
  let sB := towerDerivedEvaluationTransition D t
  have heq : Functor.whiskerLeft RT sB ≫ (β n).hom =
      (β m).hom ≫ Functor.whiskerRight sA R := by
    apply TowerRightDerivedEvaluation.derived_ext enoughT
    intro I hI
    let u := DerivedCategory.Q.map
      ((S.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex
        ((CategoryTheory.evaluation ℕᵒᵖ E).map t) (.up ℤ)).app I))
    have hna : (a m).app I ≫ sB.app (RT.obj (DerivedCategory.Q.obj I)) =
        u ≫ (a n).app I := by
      change ((EB m).mapDerivedCategoryFactors.inv.app (FTc.obj I) ≫
        (EB m).mapDerivedCategory.map (T.unit.app I)) ≫ sB.app _ = _
      rw [Category.assoc, sB.naturality, ← Category.assoc]
      rw [TowerRightDerivedEvaluation.towerTransition_inv_fac, Category.assoc]
      rfl
    have hnb : (b m).app I ≫ R.map (sA.app (DerivedCategory.Q.obj I)) =
        u ≫ (b n).app I := by
      change (P.unit.app (((EA m).mapHomologicalComplex (.up ℤ)).obj I) ≫
        R.map ((EA m).mapDerivedCategoryFactors.inv.app I)) ≫ R.map _ = _
      erw [Category.assoc, ← R.map_comp,
        TowerRightDerivedEvaluation.towerTransition_inv_fac, R.map_comp]
      erw [← Category.assoc, ← η.naturality, Category.assoc]
      rfl
    have := ha m I hI
    change sB.app _ ≫ (β n).hom.app _ = (β m).hom.app _ ≫ R.map (sA.app _)
    apply (cancel_epi ((a m).app I)).mp
    rw [← Category.assoc, hna, Category.assoc, hβ n I]
    rw [← Category.assoc, hβ m I]
    exact hnb.symm
  exact NatTrans.congr_app heq M

end GenericTower

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem coefficientSectionsRestriction
    {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) :
    sequenceCoefficientSections S = sequenceCoefficientRestriction f ⋙
      sequenceCoefficientSections R := by
  unfold sequenceCoefficientSections
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem coefficientSectionsRestriction_twice
    {R S T : Sheaf J CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ T) :
    sequenceCoefficientSections T = sequenceCoefficientRestriction g ⋙
      sequenceCoefficientRestriction f ⋙ sequenceCoefficientSections R := by
  unfold sequenceCoefficientSections
  rfl

private theorem coefficientScalarComputes
    (P : ∀ R : Sheaf J CommRingCat.{w},
      SequenceSectionsDerivedPair (sequenceCoefficientSections R))
    (hG : ∀ R : Sheaf J CommRingCat.{w},
      IsGrothendieckAbelian.{w} (sequenceCoefficientModules R))
    {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
    (I : CochainComplex (sequenceCoefficientModules S) ℤ) (hI : I.IsKInjective) :
    IsIso ((P R).unit.app
      (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj I)) := by
  let := hG R
  let E := sequenceCoefficientRestriction f
  let L := (E.mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨K, hK, j, hj, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective L
  have := hq
  have hsec : QuasiIso (((sequenceCoefficientSections R).mapHomologicalComplex (.up ℤ)).map j) :=
    coefficientRestrictionSections_quasiIso f I K j
  have := (P R).computes K hK
  have hn := (P R).unit.naturality j
  dsimp only [Functor.comp_map] at hn
  have hi : IsIso ((P R).unit.app L ≫ (P R).functor.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((P R).functor.map (DerivedCategory.Q.map j))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientScalarComparison
    (P : ∀ R : Sheaf J CommRingCat.{w},
      SequenceSectionsDerivedPair (sequenceCoefficientSections R))
    (hG : ∀ R : Sheaf J CommRingCat.{w},
      IsGrothendieckAbelian.{w} (sequenceCoefficientModules R)) :
    ∃ σ : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S),
      (P S).functor ≅ (sequenceCoefficientRestriction f).mapDerivedCategory ⋙ (P R).functor,
      ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
        (K : CochainComplex (sequenceCoefficientModules S) ℤ),
        HEq ((P S).unit.app K ≫ (σ f).hom.app (DerivedCategory.Q.obj K))
          ((P R).unit.app
            (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj K) ≫
            (P R).functor.map
              ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.inv.app K)) := by
  classical
  have ex {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) :
      ∃ e : (P S).functor ≅ (sequenceCoefficientRestriction f).mapDerivedCategory ⋙
          (P R).functor,
        ∀ K : CochainComplex (sequenceCoefficientModules S) ℤ,
          HEq ((P S).unit.app K ≫ e.hom.app (DerivedCategory.Q.obj K))
            ((P R).unit.app
              (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj K) ≫
              (P R).functor.map
                ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.inv.app K)) := by
    let := hG S
    exact scalarComparisonExists (sequenceCoefficientRestriction f)
      (sequenceCoefficientSections R) (sequenceCoefficientSections S) (P R) (P S)
      (coefficientSectionsRestriction f) (coefficientScalarComputes P hG f)
  let σ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) := (ex f).choose
  refine ⟨@σ, ?_⟩
  intro R S f K
  exact (ex f).choose_spec K

private theorem natTrans_identity
    {E D : Type*} [Category E] [Category D] (F G : E ⥤ D)
    (η : F ⟶ G) (h : F = G)
    (hη : ∀ X, HEq (η.app X) (𝟙 (G.obj X))) : HEq η (𝟙 G) := by
  subst G
  apply heq_of_eq
  apply NatTrans.ext
  funext X
  exact eq_of_heq (hη X)

private theorem map_identity
    {E D : Type*} [Category E] [Category D] (G : E ⥤ D)
    {X Y : E} (f : X ⟶ Y) (h : X = Y) (hf : HEq f (𝟙 Y)) :
    HEq (G.map f) (𝟙 (G.obj Y)) := by
  subst Y
  have he := eq_of_heq hf
  subst f
  rw [G.map_id]

private theorem complex_identity
    {E D : Type*} [Category E] [Category D] [Preadditive E] [Preadditive D]
    (F G : E ⥤ D) [F.Additive] [G.Additive] (η : F ⟶ G)
    (h : F = G) (hη : HEq η (𝟙 G)) (K : CochainComplex E ℤ) :
    HEq ((NatTrans.mapHomologicalComplex η (.up ℤ)).app K)
      (𝟙 ((G.mapHomologicalComplex (.up ℤ)).obj K)) := by
  subst G
  have he := eq_of_heq hη
  subst η
  simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  rfl

private theorem complex_scalar_identity
    {E F D : Type*} [Category E] [Category F] [Category D]
    [Preadditive E] [Preadditive F] [Preadditive D]
    (r s : E ⥤ F) [r.Additive] [s.Additive]
    (G : F ⥤ D) [G.Additive] (c : r ≅ s)
    (h : r ⋙ G = s ⋙ G) (hc : HEq (Functor.whiskerRight c.hom G) (𝟙 (s ⋙ G)))
    (K : CochainComplex E ℤ) :
    HEq ((G.mapHomologicalComplex (.up ℤ)).map
      ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K))
      (𝟙 ((G.mapHomologicalComplex (.up ℤ)).obj
        ((s.mapHomologicalComplex (.up ℤ)).obj K))) := by
  exact complex_identity (r ⋙ G) (s ⋙ G) (Functor.whiskerRight c.hom G) h hc K


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
private theorem coefficientScalarCompositionSections
    {R S T : Sheaf J CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ T)
    (k : R ⟶ T) (hk : k = f ≫ g) (K : CochainComplex (sequenceCoefficientModules T) ℤ) :
    HEq (((sequenceCoefficientSections R).mapHomologicalComplex (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (systemScalarRestrictionComposition f g k hk)
        (.up ℤ)).hom.app K)) (𝟙 (((sequenceCoefficientSections R).mapHomologicalComplex
          (.up ℤ)).obj (((sequenceCoefficientRestriction k).mapHomologicalComplex
            (.up ℤ)).obj K))) := by
  apply complex_scalar_identity
    (sequenceCoefficientRestriction g ⋙ sequenceCoefficientRestriction f)
    (sequenceCoefficientRestriction k) (sequenceCoefficientSections R)
    (systemScalarRestrictionComposition f g k hk) ?_ ?_ K
  · exact (coefficientSectionsRestriction_twice f g).symm.trans
      (coefficientSectionsRestriction k)
  · apply natTrans_identity _ _ _
      ((coefficientSectionsRestriction_twice f g).symm.trans (coefficientSectionsRestriction k))
    intro M
    let G := toSheaf (derivedChangeRingIndependentCoefficients J R) ⋙
      sheafToPresheaf J AddCommGrpCat.{w}
    have hm : HEq (G.map ((systemScalarRestrictionComposition f g k hk).hom.app M))
        (𝟙 (G.obj ((sequenceCoefficientRestriction k).obj M))) := by
      apply heq_of_eq
      ext U x
      exact ModuleCat.restrictScalarsComp'App_inv_apply (f.hom.app U).hom
        (g.hom.app U).hom (k.hom.app U).hom
        (congrArg (fun t ↦ (t.hom.app U).hom) hk) (M.val.obj U) x
    exact map_identity lim _ rfl hm

private theorem map_comp_identity
    {E D : Type*} [Category E] [Category D] (F : E ⥤ D)
    {X Y : E} (f : X ⟶ Y) (h : X = Y) (hf : HEq f (𝟙 Y))
    {Z : D} (g : F.obj Y ⟶ Z) : HEq (F.map f ≫ g) g := by
  subst Y
  have he := eq_of_heq hf
  subst f
  simp only [F.map_id, Category.id_comp]
  rfl

private theorem complex_obj_congr
    {E D : Type*} [Category E] [Category D] [Preadditive E] [Preadditive D]
    (F G : E ⥤ D) [F.Additive] [G.Additive] (h : F = G) (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj K = (G.mapHomologicalComplex (.up ℤ)).obj K := by
  subst G
  rfl

private theorem complex_scalar_objects
    {E F D : Type*} [Category E] [Category F] [Category D]
    [Preadditive E] [Preadditive F] [Preadditive D]
    (r s : E ⥤ F) [r.Additive] [s.Additive]
    (G : F ⥤ D) [G.Additive] (h : r ⋙ G = s ⋙ G) (K : CochainComplex E ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((r.mapHomologicalComplex (.up ℤ)).obj K) =
      (G.mapHomologicalComplex (.up ℤ)).obj ((s.mapHomologicalComplex (.up ℤ)).obj K) := by
  exact complex_obj_congr (r ⋙ G) (s ⋙ G) h K

private theorem coefficientScalarCocycle
    (P : ∀ R : Sheaf J CommRingCat.{w},
      SequenceSectionsDerivedPair (sequenceCoefficientSections R))
    (σ : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S),
      (P S).functor ≅ (sequenceCoefficientRestriction f).mapDerivedCategory ⋙ (P R).functor)
    (hσ : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
      (K : CochainComplex (sequenceCoefficientModules S) ℤ),
      HEq ((P S).unit.app K ≫ (σ f).hom.app (DerivedCategory.Q.obj K))
        ((P R).unit.app
          (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj K) ≫
          (P R).functor.map
            ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.inv.app K)))
    {R S T : Sheaf J CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ T)
    (k : R ⟶ T) (hk : k = f ≫ g) :
    (σ g).hom ≫ Functor.whiskerLeft (sequenceCoefficientRestriction g).mapDerivedCategory
        (σ f).hom ≫ Functor.whiskerRight
          (Functor.exactDerivedRestrictionComposition
            (sequenceCoefficientRestriction g) (sequenceCoefficientRestriction f)
            (sequenceCoefficientRestriction k)
            (systemScalarRestrictionComposition f g k hk)).hom (P R).functor =
      (σ k).hom := by
  refine derivedScalarCocycle (sequenceCoefficientRestriction g) (sequenceCoefficientRestriction f)
    (sequenceCoefficientRestriction k) (sequenceCoefficientSections R) (P R)
    (sequenceCoefficientSections S) (sequenceCoefficientSections T) (P S) (P T)
    ?_ ?_ (σ f) (σ g) (σ k) (systemScalarRestrictionComposition f g k hk) ?_ ?_ ?_
  · exact coefficientSectionsRestriction f
  · exact coefficientSectionsRestriction_twice f g
  · exact hσ f
  · exact hσ g
  · intro K
    have hid := coefficientScalarCompositionSections f g k hk K
    have ho := complex_scalar_objects
      (sequenceCoefficientRestriction g ⋙ sequenceCoefficientRestriction f)
      (sequenceCoefficientRestriction k) (sequenceCoefficientSections R)
      ((coefficientSectionsRestriction_twice f g).symm.trans (coefficientSectionsRestriction k)) K
    have hh := map_comp_identity DerivedCategory.Q _ ho hid
      ((P R).unit.app (((sequenceCoefficientRestriction k).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (P R).functor.map ((sequenceCoefficientRestriction k).mapDerivedCategoryFactors.inv.app K))
    exact (hσ k K).trans hh.symm

omit [EssentiallySmall.{w} C] in
private theorem coefficientRestrictionTransition
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α)
    {m n : ℕ} (h : m ≤ n) :
    Functor.whiskerLeft r.functor
        ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).map (homOfLE h).op) ≫
        (r.evaluation m).hom =
      (r.evaluation n).hom ≫
        Functor.whiskerRight (strictSystemTransition B h)
          (sequenceCoefficientRestriction (α.app (op n))) ≫
        Functor.whiskerLeft (systemEvaluation B m)
          (systemScalarRestrictionComposition (α.app (op n)) (B.map (homOfLE h).op)
            (α.app (op m)) (by simpa using α.naturality (homOfLE h).op)).hom := by
  apply NatTrans.ext
  funext M
  ext U x
  have hr := r.transitions M h U x
  change _ = _
  exact eq_of_heq hr




set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [EssentiallySmall.{w} C] in
private theorem coefficientRestrictionDerivedTransition
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α)
    {m n : ℕ} (h : m ≤ n) :
    Functor.whiskerLeft r.functor.mapDerivedCategory
        (towerDerivedEvaluationTransition (sequenceCoefficientModules A) (homOfLE h).op) ≫
        (sequenceRestrictionDerivedEvaluation r m).hom =
      (sequenceRestrictionDerivedEvaluation r n).hom ≫
        Functor.whiskerRight (systemDerivedTransition B h)
          (sequenceCoefficientRestriction (α.app (op n))).mapDerivedCategory ≫
        Functor.whiskerLeft (derivedSystemEvaluation B m)
          (Functor.exactDerivedRestrictionComposition
            (systemRestriction B h) (sequenceCoefficientRestriction (α.app (op n)))
            (sequenceCoefficientRestriction (α.app (op m)))
            (systemScalarRestrictionComposition (α.app (op n)) (B.map (homOfLE h).op)
              (α.app (op m)) (by simpa using α.naturality (homOfLE h).op))).hom := by
  exact canonicalSquareTransition
    (C := StrictRingSystem B) (D := ℕᵒᵖ ⥤ sequenceCoefficientModules A)
    (E := sequenceCoefficientModules (B.obj (op n)))
    (F := sequenceCoefficientModules (B.obj (op m))) (G := sequenceCoefficientModules A)
    r.functor
    ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj (op n))
    ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj (op m))
    (systemEvaluation B n) (systemEvaluation B m) (systemRestriction B h)
    (sequenceCoefficientRestriction (α.app (op n)))
    (sequenceCoefficientRestriction (α.app (op m)))
    (systemScalarRestrictionComposition (α.app (op n)) (B.map (homOfLE h).op)
      (α.app (op m)) (by simpa using α.naturality (homOfLE h).op))
    (r.evaluation n) (r.evaluation m)
    ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).map (homOfLE h).op)
    (strictSystemTransition B h)
    (towerDerivedEvaluationTransition (sequenceCoefficientModules A) (homOfLE h).op)
    (systemDerivedTransition B h)
    (TowerRightDerivedEvaluation.towerTransition_fac
      (sequenceCoefficientModules A) (homOfLE h).op)
    (systemDerivedTransition_rep B h) (coefficientRestrictionTransition r h)



private theorem inverse_cocycle
    {D : Type*} [Category D] {A B C E F G : D}
    (sx : A ≅ B) (sy : C ≅ E) (sg : F ≅ C) (sk : F ≅ G)
    (t : A ⟶ C) (a : B ⟶ E) (c : E ⟶ G)
    (hn : t ≫ sy.hom = sx.hom ≫ a)
    (hc : sg.hom ≫ sy.hom ≫ c = sk.hom) :
    a ≫ c ≫ sk.inv = sx.inv ≫ t ≫ sg.inv := by
  apply (cancel_epi sx.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← hn, Category.assoc]
  have hi : sy.hom ≫ c ≫ sk.inv = sg.inv := by
    apply (cancel_epi sg.hom).mp
    have hc' := congrArg (fun q ↦ q ≫ sk.inv) hc
    simpa only [Category.assoc, Iso.hom_inv_id] using hc'
  exact congrArg (t ≫ ·) hi

private theorem finite_transition_composition
    {D : Type*} [Category D] {Vn Vm An Am Bn Bm C Sn T Sm : D}
    (t : Vn ⟶ Vm) (bm : Vm ⟶ Am) (bn : Vn ⟶ An)
    (pm : Am ⟶ Bm) (pn : An ⟶ Bn) (td : An ⟶ Am)
    (a : Bn ⟶ C) (c : C ⟶ Bm) (sm : Bm ⟶ Sm) (sn : Bn ⟶ Sn)
    (τ : Sn ⟶ T) (sg : T ⟶ Sm)
    (hβ : t ≫ bm = bn ≫ td) (hr : td ≫ pm = pn ≫ a ≫ c)
    (hs : a ≫ c ≫ sm = sn ≫ τ ≫ sg) :
    t ≫ bm ≫ pm ≫ sm = bn ≫ pn ≫ sn ≫ τ ≫ sg := by
  calc
    _ = (t ≫ bm) ≫ pm ≫ sm := by simp only [Category.assoc]
    _ = (bn ≫ td) ≫ pm ≫ sm := by rw [hβ]
    _ = bn ≫ (td ≫ pm) ≫ sm := by simp only [Category.assoc]
    _ = bn ≫ (pn ≫ a ≫ c) ≫ sm := by rw [hr]
    _ = bn ≫ pn ≫ (a ≫ c ≫ sm) := by simp only [Category.assoc]
    _ = _ := by rw [hs]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientFiniteTransition
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α)
    (hσ : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
      (K : CochainComplex (sequenceCoefficientModules S) ℤ),
      HEq ((d.finite S).unit.app K ≫ (d.scalar f).hom.app (DerivedCategory.Q.obj K))
        ((d.finite R).unit.app
          (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj K) ≫
          (d.finite R).functor.map
            ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.inv.app K)))
    (hβ : ∀ {m n : ℕ} (h : m ≤ n)
      (M : DerivedCategory (ℕᵒᵖ ⥤ sequenceCoefficientModules A)),
      (towerDerivedEvaluationTransition AddCommGrpCat.{w} (homOfLE h).op).app
          (d.tower.functor.obj M) ≫ (d.evaluation m).hom.app M =
        (d.evaluation n).hom.app M ≫ (d.finite A).functor.map
          ((towerDerivedEvaluationTransition (sequenceCoefficientModules A)
            (homOfLE h).op).app M))
    {m n : ℕ} (h : m ≤ n) (M : DerivedCategory (StrictRingSystem B)) :
    (towerDerivedEvaluationTransition AddCommGrpCat.{w} (homOfLE h).op).app
        (d.global.obj M) ≫ (d.finiteEvaluation m).hom.app M =
      (d.finiteEvaluation n).hom.app M ≫
        (d.finite (B.obj (op n))).functor.map ((systemDerivedTransition B h).app M) ≫
        (d.scalar (B.map (homOfLE h).op)).inv.app ((derivedSystemEvaluation B m).obj M) := by
  let rn := sequenceCoefficientRestriction (α.app (op n))
  let rm := sequenceCoefficientRestriction (α.app (op m))
  let b := systemRestriction B h
  let c := systemScalarRestrictionComposition (α.app (op n)) (B.map (homOfLE h).op)
    (α.app (op m)) (by simpa using α.naturality (homOfLE h).op)
  let cd := Functor.exactDerivedRestrictionComposition b rn rm c
  let X := (derivedSystemEvaluation B n).obj M
  let Y := (derivedSystemEvaluation B m).obj M
  let τ := (systemDerivedTransition B h).app M
  have hc := NatTrans.congr_app
    (coefficientScalarCocycle d.finite (@d.scalar) hσ (α.app (op n))
      (B.map (homOfLE h).op) (α.app (op m)) (by simpa using α.naturality (homOfLE h).op)) Y
  change (d.scalar (B.map (homOfLE h).op)).hom.app Y ≫
      (d.scalar (α.app (op n))).hom.app (b.mapDerivedCategory.obj Y) ≫
      (d.finite A).functor.map (cd.hom.app Y) =
    (d.scalar (α.app (op m))).hom.app Y at hc
  have hn := (d.scalar (α.app (op n))).hom.naturality τ
  dsimp only [Functor.comp_map] at hn
  have hs : (d.finite A).functor.map (rn.mapDerivedCategory.map τ) ≫
      (d.finite A).functor.map (cd.hom.app Y) ≫
      (d.scalar (α.app (op m))).inv.app Y =
    (d.scalar (α.app (op n))).inv.app X ≫
      (d.finite (B.obj (op n))).functor.map τ ≫
      (d.scalar (B.map (homOfLE h).op)).inv.app Y := by
    exact inverse_cocycle
      ((d.scalar (α.app (op n))).app X)
      ((d.scalar (α.app (op n))).app (b.mapDerivedCategory.obj Y))
      ((d.scalar (B.map (homOfLE h).op)).app Y) ((d.scalar (α.app (op m))).app Y)
      ((d.finite (B.obj (op n))).functor.map τ)
      ((d.finite A).functor.map (rn.mapDerivedCategory.map τ))
      ((d.finite A).functor.map (cd.hom.app Y)) hn hc
  have hr := NatTrans.congr_app (coefficientRestrictionDerivedTransition d.restriction h) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hr
  have hr' := congrArg (d.finite A).functor.map hr
  dsimp only [SequenceSectionsComparisons.finiteEvaluation,
    SequenceSectionsComparisons.restrictedEvaluation, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
  simp only [Category.assoc]
  refine finite_transition_composition _ _ _ _ _
    ((d.finite A).functor.map
      ((towerDerivedEvaluationTransition (sequenceCoefficientModules A)
        (homOfLE h).op).app (d.restriction.functor.mapDerivedCategory.obj M)))
    ((d.finite A).functor.map (rn.mapDerivedCategory.map τ))
    ((d.finite A).functor.map (cd.hom.app Y)) _ _ _ _ ?_ ?_ hs
  · exact hβ h _
  · simpa only [Functor.map_comp] using hr'



private theorem mapped_forward_normalization
    {E D : Type*} [Category E] [Category D] (F : E ⥤ D)
    {X Y : E} {A : D} (u : A ⟶ F.obj X) (v : A ⟶ F.obj Y) (e : X ≅ Y)
    (h : u = v ≫ F.map e.inv) : u ≫ F.map e.hom = v := by
  rw [h, Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientNormalization
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α)
    (hβunit : ∀ (n : ℕ)
    (I : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ), I.IsKInjective →
    ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategoryFactors.inv.app
        (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj I) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory.map
        (d.tower.unit.app I) ≫
      (d.evaluation n).hom.app (DerivedCategory.Q.obj I) ≫
      (d.finite A).functor.map
        (((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app I) =
      (d.finite A).unit.app
        ((((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj I))
    (hσ : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
    (K : CochainComplex (sequenceCoefficientModules S) ℤ),
    HEq ((d.finite S).unit.app K ≫ (d.scalar f).hom.app (DerivedCategory.Q.obj K))
      ((d.finite R).unit.app
        (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (d.finite R).functor.map
          ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.inv.app K)))
    (hβ : ∀ {m n : ℕ} (h : m ≤ n)
    (M : DerivedCategory (ℕᵒᵖ ⥤ sequenceCoefficientModules A)),
    (towerDerivedEvaluationTransition AddCommGrpCat.{w} (homOfLE h).op).app
        (d.tower.functor.obj M) ≫ (d.evaluation m).hom.app M =
      (d.evaluation n).hom.app M ≫ (d.finite A).functor.map
        ((towerDerivedEvaluationTransition (sequenceCoefficientModules A)
          (homOfLE h).op).app M)) : d.Normalized := by
  refine ⟨hβunit, ?_, hβ, coefficientFiniteTransition d hσ hβ⟩
  intro R S f K
  simpa only [Category.assoc, Iso.app_hom] using
    mapped_forward_normalization (d.finite R).functor _ _
      ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.app K)
      (eq_of_heq (hσ f K))

/-- Unbounded termwise derived global sections of strict coefficient systems exist,
with the two specified natural comparisons and their actual transition normalization.
Source: Stacks Project, Cohomology on Sites, Tags 0941 and 0D6E
(blueprint: lem-coef-sequence-global-sections-evaluation).

Proof plan:
1. Restriction changes only the scalar action, hence preserves sectionwise kernels and
   sheafified sectionwise cokernels (`def-weil-sheaf-of-modules-category`). Compatibility
   of α makes all transitions A-linear. Thus U⁰ is exact componentwise, and localizes to U
   (`lem-weil-tower-category-levelwise-abelian`,
   `lem-weil-pbc-exact-functor-derived-factorization`, `def-pc-sheaf-restrict-scalars`).
2. Constant-A towers form a Grothendieck category by
   `lem-weil-pbc-small-module-diagrams-grothendieck`. Apply
   `lem-weil-pbc-kinjective-functorial-existence` to get a simultaneous resolution.
   Individual coefficient categories have resolutions by `prop-pur-kinjective-resolutions-exist`.
   No cohomological bounds or exactness of infinite products are required.
3. Termwise sections are additive and preserve homotopies and mapping cones. Apply
   `lem-weil-pbc-kinjective-total-derived` to obtain the total derived pair on towers.
   Its composite with exact U is the actual functor G on the ordinary derived category.
4. A constant-A K-injective tower evaluates to K-injectives by
   `lem-weil-tower-evaluation-kinjective`. Its resolution maps evaluate to quasi-isomorphisms.
   The two derived units identify both evaluations with sections of the same resolution.
   `lem-weil-pbc-kinjective-hom-derived` gives naturality on derived morphisms; the same
   calculation on transition maps proves evaluation_transition.
5. Scalar restriction is the direct image of the identity ringed-topos morphism by
   `lem-weil-pbc-restriction-ringed-topos-module-direct-image`. Compose with the global-sections
   morphism to the singleton Z-ringed site (`def-weil-pbc-ringed-topos-morphism`,
   `def-weil-pbc-constant-sheaf`, `lem-weil-pbc-singleton-site-module-comparison`). The comparison
   of `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is invertible. Its unit equation
   is scalar_unit; uniqueness in `lem-weil-pbc-kinjective-total-derived` fixes this comparison.
6. For composable coefficient maps, both the direct scalar comparison and the composite
   scalar comparisons have the same derived-unit equation. Uniqueness makes them equal.
   The identity comparison is likewise the identity, with the canonical restriction identifications.
7. Naturality and this composition equality identify the derived-sections transition with
   the inverse scalar comparison after the sections map of J_n → Res J_m. Combining with
   Step 4 proves finite_transition. All comparisons are natural isomorphisms of functors,
   including identity and iterated transitions. No varying-ring evaluation is claimed to
   preserve K-injectives. -/
theorem coefficientSequenceGlobalSectionsEvaluation
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) :
    ∃ d : SequenceSectionsComparisons B A α, d.Normalized := by
  classical
  have hG (R : Sheaf J CommRingCat.{w}) :
      IsGrothendieckAbelian.{w} (sequenceCoefficientModules R) :=
    isGrothendieckAbelian_coefficientUniverse
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  have hp (R : Sheaf J CommRingCat.{w}) :
      Nonempty (SequenceSectionsDerivedPair (sequenceCoefficientSections R)) := by
    let := hG R
    exact sectionsPairExists _
  let P (R : Sheaf J CommRingCat.{w}) := Classical.choice (hp R)
  let := hG A
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ sequenceCoefficientModules A) :=
    sectionsTowerGrothendieck
  let T := Classical.choice (sectionsPairExists (sequenceTowerSections A))
  have enoughT (K : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ) :
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ) (a : K ⟶ I),
        I.IsKInjective ∧ QuasiIso a := by
    obtain ⟨I, hI, a, ha, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, a, hI, hq⟩
  obtain ⟨β, hβ, htβ⟩ := coefficientTowerComparison (sequenceCoefficientSections A) (P A) T enoughT
  obtain ⟨σ, hσ⟩ := coefficientScalarComparison P hG
  let d : SequenceSectionsComparisons B A α :=
    ⟨coefficientRestrictionData B A α, P, T, fun n ↦ β (op n), @σ⟩
  refine ⟨d, coefficientNormalization d ?_ ?_ ?_⟩
  · intro n I hI
    exact hβ (op n) I
  · intro R S f K
    exact hσ f K
  · intro m n h M
    exact htβ (op n) (op m) (homOfLE h).op M

end SheafOfModules
