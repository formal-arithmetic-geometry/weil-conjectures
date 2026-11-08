/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import Submission.WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
public import Submission.WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Submission.WeilConjectures.CategoryTheory.TowerRightDerivedEvaluation.TowerRightDerivedEvaluation
import all Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

end Generic

section GenericScalar

universe c cv dc

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

end SheafOfModules
