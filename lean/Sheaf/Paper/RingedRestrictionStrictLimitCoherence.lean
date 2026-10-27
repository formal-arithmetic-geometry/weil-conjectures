/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.CategoryTheory.TowerLimitTransposeNormalization
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Mathlib.CategoryTheory.Limits.Types.Products
import all Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
import all Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import all Sheaf.Paper.ExactProductFunctorStrictLimit
import all Sheaf.Paper.ExactProductFunctorRoosResolution
import Sheaf.CategoryTheory.StrictRoosDerivation
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Actual sections restriction and normalized strict derived limits

Source: Stacks Project, sites-cohomology.tex, Tags 0940, 0941, 0A07 and 0D6E;
blueprint det-sf-comp-coherence-refinement (2), integral comparison
(blueprint: lem-sfb-ringed-restriction-strict-limit-coherence).

All helpers specialize existing functors. The ordinary sections comparison is fixed by
its geometric-adjunction equation on every global section. The resolution equations fix
actual derived restrictions, rather than arbitrary transformations with the same endpoints.
- Realization of positive levels uses `op n` for level n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w a v b z e ev
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedRestrictionLimit

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors UnboundedExactTower.cochainUnit


/-- Actual underlying-module sections at the terminal object.
Source: Stacks 01FT (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
abbrev sections {C : Type u} [SmallCategory C] [HasTerminal C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    ringedSiteModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op (⊤_ C))

/-- Reuse additivity of evaluation and forgetting scalars.
Source: Stacks 01FT (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
instance sectionsAdditive {C : Type u} [SmallCategory C] [HasTerminal C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) : (sections R).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf R ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op (⊤_ C))).Additive

/-- The constant singleton sheaf, the terminal object of the set topos.
Source: Stacks 00XA (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
abbrev singleton {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :=
  Sheaf.terminal J (Types.isTerminalPUnit : IsTerminal (PUnit : Type u))

/-- The actual map from the terminal sheaf determined by a section at the terminal object.
Source: Stacks 01FT (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def sectionMap {C : Type u} [SmallCategory C] [HasTerminal C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    (M : ringedSiteModules.{u} R) (x : (sections R).obj M) :
    singleton J ⟶ (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M) :=
  ⟨{ app := fun U ↦ ↾fun _ ↦ M.val.map (terminal.from U.unop).op x
     naturality := by
       intro U V f
       ext t
       change M.val.map (terminal.from V.unop).op x =
         M.val.map f (M.val.map (terminal.from U.unop).op x)
       rw [← M.val.map_comp_apply]
       have h : (terminal.from V.unop).op = (terminal.from U.unop).op ≫ f :=
         Subsingleton.elim _ _
       rw [h] }⟩

/-- Ordinary direct-image/sections comparison, characterized by the geometric adjunction.
This equation determines the comparison on every section, including nonconstant modules.
Source: Stacks 0D6E (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def IsSectionsComparison {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasTerminal C] [HasTerminal D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism S R) (c : f.modules ⋙ sections R ≅ sections S) : Prop :=
  ∀ (M : ringedSiteModules.{u} S) (x : (sections R).obj (f.modules.obj M)),
    (f.adj.homEquiv _ _).symm
        (sectionMap R (f.modules.obj M) x ≫ f.underlying.hom.app M) =
      (Sheaf.isTerminalTerminal K Types.isTerminalPUnit).from (f.inverse.obj (singleton J)) ≫
        sectionMap S M ((c.hom.app M) x)

/-- Actual postcomposition on strict inverse sequences.
Source: Stacks 0940 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
abbrev tower {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    (F : A ⥤ B) := (Functor.whiskeringRight ℕᵒᵖ A B).obj F

/-- Ordinary inverse limit, using the shared tower-limit abbreviation and instances.
Source: Stacks 0940 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
abbrev limitFunctor (A : Type a) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] := TowerLimitTransposeNormalization.towerLimit A

/-- The ordinary comparison of a functor with a termwise strict inverse limit.
Source: Stacks 0940 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def limitMap {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj
        (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I) ⟶
      ((limitFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((tower F).mapHomologicalComplex (.up ℤ)).obj I) where
  f i := limit.post (I.X i) F
  comm' i j _ := (limit.map_post (I.d i j) F).symm

/-- Reuse the cochain comparison of the existing K-injective right derived functor.
Source: Stacks 070I (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
abbrev unit {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (I : CochainComplex A ℤ) := UnboundedExactTower.cochainUnit F I

/-- The normalized comparison of a right adjoint with total strict inverse limit.
It is specified on complexes by the common underived direct-image composite.
Source: Stacks 0A07 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def IsLimitComparison
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive]
    (c : (limitFunctor A).rightDerivedFunctor ⋙ F.rightDerivedFunctor ≅
      (tower F).rightDerivedFunctor ⋙ (limitFunctor B).rightDerivedFunctor) : Prop :=
  ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    unit F (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        F.rightDerivedFunctor.map (unit (limitFunctor A) I) ≫
        c.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (limitMap F I) ≫
        unit (limitFunctor B) (((tower F).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (limitFunctor B).rightDerivedFunctor.map (unit (tower F) I)

/-- Actual restriction on representatives: apply sections to the adjunct of v.
Source: Stacks 09T5, 0D6E (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def restrictionMap {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] {E : Type e} [Category.{ev} E] [Abelian E]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (I : CochainComplex A ℤ) (T : CochainComplex B ℤ)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) :
    (H.mapHomologicalComplex (.up ℤ)).obj I ⟶ (H'.mapHomologicalComplex (.up ℤ)).obj T :=
  (H.mapHomologicalComplex (.up ℤ)).map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv I T v) ≫
    (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app T

/-- The K-injective computation specifying actual restriction, including its unit.
Source: Stacks 09T5, 0D6E (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def IsRestriction
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] {E : Type e} [Category.{ev} E] [Abelian E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (rho : H.rightDerivedFunctor ⟶ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor) : Prop :=
  ∀ (I : CochainComplex A ℤ) (T : CochainComplex B ℤ)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ T),
    I.IsKInjective → T.IsKInjective → QuasiIso v →
      unit H I ≫ rho.app (DerivedCategory.Q.obj I) ≫
          H'.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app I) ≫
          H'.rightDerivedFunctor.map (DerivedCategory.Q.map v) =
        DerivedCategory.Q.map (restrictionMap F G adj H H' c I T v) ≫ unit H' T

/-- Resolution normalization of the exact-product inverse-image comparison.
Source: Stacks 0941 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def IsInverseLimitComparison
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (lambda : (limitFunctor A).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      (tower F).mapDerivedCategory ⋙ (limitFunctor B).rightDerivedFunctor) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (T : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (v : ((tower F).mapHomologicalComplex (.up ℤ)).obj I ⟶ T),
    I.IsKInjective → T.IsKInjective → QuasiIso v →
      F.mapDerivedCategory.map (unit (limitFunctor A) I) ≫
          lambda.hom.app (DerivedCategory.Q.obj I) ≫
          (limitFunctor B).rightDerivedFunctor.map
            ((tower F).mapDerivedCategoryFactors.hom.app I) ≫
          (limitFunctor B).rightDerivedFunctor.map (DerivedCategory.Q.map v) =
        F.mapDerivedCategoryFactors.hom.app
            (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map (limitMap F I ≫
            ((limitFunctor B).mapHomologicalComplex (.up ℤ)).map v) ≫
          unit (limitFunctor B) T

/-- The ordinary-limit inclusion into the existing strict Roos cone.
Source: Stacks 0941 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def limitInclusion {A : Type a} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I ⟶ roosF.obj I :=
  roosAugment (fun n ↦ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)
    (by intro n; ext i; exact limit.w (I.X i) (homOfLE (Nat.le_succ n)).op)

/-- The normalized Roos comparison, using the same chosen derived limit everywhere.
Source: Stacks 0941 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def IsRoosComparison {A : Type a} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (theta : roosF ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor A).rightDerivedFunctor) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
    (∀ i : ℤ, Injective (I.X i)) →
      DerivedCategory.Q.map (limitInclusion I) ≫ theta.hom.app I = unit (limitFunctor A) I

/-- Exact evaluation on the derived category of strict towers.
Source: Stacks 0940 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
abbrev evaluate {A : Type a} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] (n : ℕᵒᵖ) :=
  ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory

/-- Evaluation comparisons are fixed by their derived-unit equations and include every
transition in the index category.
Source: Stacks 0A07 (blueprint: lem-sfb-ringed-restriction-strict-limit-coherence). -/
def IsEvaluationComparison
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (F : A ⥤ B) [F.Additive]
    (e : ∀ n : ℕᵒᵖ, (tower F).rightDerivedFunctor ⋙ evaluate n ≅
      evaluate n ⋙ F.rightDerivedFunctor) : Prop :=
  (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
    (evaluate n).map (unit (tower F) I) ≫ (e n).hom.app (DerivedCategory.Q.obj I) ≫
        F.rightDerivedFunctor.map
          (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app I) =
      ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app
          (((tower F).mapHomologicalComplex (.up ℤ)).obj I) ≫ unit F (I.asFunctor.obj n)) ∧
  (∀ (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (n m : ℕᵒᵖ) (t : n ⟶ m),
    (towerDerivedEvaluationTransition B t).app ((tower F).rightDerivedFunctor.obj M) ≫
        (e m).hom.app M =
      (e n).hom.app M ≫ F.rightDerivedFunctor.map ((towerDerivedEvaluationTransition A t).app M))

private def sectionEquiv {C : Type u} [SmallCategory C] [HasTerminal C]
    {J : GrothendieckTopology C} (M : Sheaf J (Type u)) :
    M.obj.obj (op (⊤_ C)) ≃ (singleton J ⟶ M) where
  toFun x := ⟨{
    app := fun U ↦ ↾fun _ ↦ M.obj.map (terminal.from U.unop).op x
    naturality := by
      intro U V f
      ext t
      change M.obj.map (terminal.from V.unop).op x =
        M.obj.map f (M.obj.map (terminal.from U.unop).op x)
      rw [← Functor.map_comp_apply]
      exact congrArg (fun g : op (⊤_ C) ⟶ V ↦ M.obj.map g x)
        (Subsingleton.elim _ _) }⟩
  invFun f := f.hom.app (op (⊤_ C)) PUnit.unit
  left_inv x := by
    change M.obj.map (terminal.from (⊤_ C)).op x = x
    rw [show terminal.from (⊤_ C) = 𝟙 _ from Subsingleton.elim _ _, op_id, M.obj.map_id]
    rfl
  right_inv f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro t
    have h := ConcreteCategory.congr_hom (f.hom.naturality (terminal.from U.unop).op)
      PUnit.unit
    exact h.symm

private def sectionsEquiv {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasTerminal C] [HasTerminal D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism S R) (M : ringedSiteModules.{u} S) :
    (sections R).obj (f.modules.obj M) ≃ (sections S).obj M := by
  have := f.leftExact
  let t : f.inverse.obj (singleton J) ≅ singleton K :=
    ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj f.inverse _).uniqueUpToIso
      (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)
  exact (sectionEquiv _).trans
    ((Iso.homCongr (Iso.refl _) (f.underlying.app M)).trans
      ((f.adj.homEquiv _ _).symm.trans
        ((Iso.homCongr t (Iso.refl _)).trans (sectionEquiv _).symm)))

private theorem sectionsEquiv_spec {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasTerminal C] [HasTerminal D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism S R) (M : ringedSiteModules.{u} S)
    (x : (sections R).obj (f.modules.obj M)) :
    (f.adj.homEquiv _ _).symm
        (sectionMap R (f.modules.obj M) x ≫ f.underlying.hom.app M) =
      (Sheaf.isTerminalTerminal K Types.isTerminalPUnit).from (f.inverse.obj (singleton J)) ≫
        sectionMap S M (sectionsEquiv f M x) := by
  have := f.leftExact
  let t : f.inverse.obj (singleton J) ≅ singleton K :=
    ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj f.inverse _).uniqueUpToIso
      (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)
  change _ = t.hom ≫ (sectionEquiv _)
    ((sectionEquiv _).symm (t.inv ≫
      (f.adj.homEquiv _ _).symm (sectionMap R (f.modules.obj M) x ≫ f.underlying.hom.app M)))
  rw [Equiv.apply_symm_apply, Iso.hom_inv_id_assoc]

private theorem sectionsEquiv_add {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasTerminal C] [HasTerminal D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism S R) (M : ringedSiteModules.{u} S)
    (x y : (sections R).obj (f.modules.obj M)) :
    sectionsEquiv f M (x + y) = sectionsEquiv f M x + sectionsEquiv f M y := by
  have := f.leftExact
  let t : f.inverse.obj (singleton J) ≅ singleton K :=
    ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj f.inverse _).uniqueUpToIso
      (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)
  let a : singleton J ⟶ (sheafCompose J (forget RingCat)).obj R :=
    ⟨{ app := fun U ↦ ↾fun _ ↦ (1 : R.obj.obj U)
       , naturality := by intro U V g; ext z; exact (R.obj.map g).hom.map_one.symm }⟩
  have h := f.module_linear M (singleton J) a
    (sectionMap R (f.modules.obj M) x) (sectionMap R (f.modules.obj M) y)
    (sectionMap R (f.modules.obj M) (x + y)) (by
      intro U z
      change (f.modules.obj M).val.map _ (x + y) = _
      change _ = (1 : R.obj.obj U) •
        (f.modules.obj M).val.map (terminal.from U.unop).op x +
        (f.modules.obj M).val.map (terminal.from U.unop).op y
      rw [map_add, one_smul]) (op (⊤_ D))
    (t.inv.hom.app (op (⊤_ D)) PUnit.unit)
  have h1 := f.ring_one (singleton J) a (by intro U z; rfl)
    (op (⊤_ D)) (t.inv.hom.app (op (⊤_ D)) PUnit.unit)
  change sectionsEquiv f M (x + y) = _ at h
  rw [h1] at h
  change sectionsEquiv f M (x + y) =
    @Add.add (M.val.obj (op (⊤_ D))) inferInstance
      (@SMul.smul (S.obj.obj (op (⊤_ D))) (M.val.obj (op (⊤_ D))) inferInstance
        1 (sectionsEquiv f M x)) (sectionsEquiv f M y) at h
  have hs : @SMul.smul (S.obj.obj (op (⊤_ D))) (M.val.obj (op (⊤_ D)))
      inferInstance 1 (sectionsEquiv f M x) = sectionsEquiv f M x :=
    one_smul (S.obj.obj (op (⊤_ D)))
      (show M.val.obj (op (⊤_ D)) from sectionsEquiv f M x)
  exact h.trans (congrArg
    (fun z : M.val.obj (op (⊤_ D)) ↦
      @Add.add (M.val.obj (op (⊤_ D))) inferInstance z (sectionsEquiv f M y)) hs)

private theorem sectionMap_naturality {C : Type u} [SmallCategory C] [HasTerminal C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    {M N : ringedSiteModules.{u} R} (v : M ⟶ N) (x : (sections R).obj M) :
    sectionMap R N ((sections R).map v x) = sectionMap R M x ≫
      ((SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)).map v) := by
  apply Sheaf.hom_ext
  ext U z
  exact (ConcreteCategory.congr_hom (v.val.naturality (terminal.from U.unop).op) x).symm

private theorem sectionsEquiv_naturality {C D : Type u}
    [SmallCategory C] [SmallCategory D] [HasTerminal C] [HasTerminal D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism S R) {M N : ringedSiteModules.{u} S} (v : M ⟶ N)
    (x : (sections R).obj (f.modules.obj M)) :
    sectionsEquiv f N ((sections R).map (f.modules.map v) x) =
      (sections S).map v (sectionsEquiv f M x) := by
  have := f.leftExact
  let t : f.inverse.obj (singleton J) ≅ singleton K :=
    ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj
      f.inverse _).uniqueUpToIso (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)
  apply (sectionEquiv
    ((SheafOfModules.toSheaf S ⋙ sheafCompose K (forget AddCommGrpCat)).obj N)).injective
  change sectionMap S N (sectionsEquiv f N ((sections R).map (f.modules.map v) x)) =
    sectionMap S N ((sections S).map v (sectionsEquiv f M x))
  apply (cancel_epi t.hom).mp
  have ht : t.hom = (Sheaf.isTerminalTerminal K Types.isTerminalPUnit).from
      (f.inverse.obj (singleton J)) := rfl
  rw [ht, ← sectionsEquiv_spec, sectionMap_naturality, sectionMap_naturality,
    ← Category.assoc, ← sectionsEquiv_spec, Category.assoc]
  have hn :
      (SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)).map
          (f.modules.map v) ≫ f.underlying.hom.app N =
        f.underlying.hom.app M ≫ f.direct.map
          ((SheafOfModules.toSheaf S ⋙ sheafCompose K (forget AddCommGrpCat)).map v) :=
    f.underlying.hom.naturality v
  rw [hn, ← Category.assoc]
  exact f.adj.homEquiv_naturality_right_symm
    (sectionMap R (f.modules.obj M) x ≫ f.underlying.hom.app M)
    ((SheafOfModules.toSheaf S ⋙ sheafCompose K (forget AddCommGrpCat)).map v)

attribute [local irreducible] sectionsEquiv

private theorem sectionsComparison_exists {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasTerminal C] [HasTerminal D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism S R) :
    ∃ c : f.modules ⋙ sections R ≅ sections S, IsSectionsComparison f c := by
  let c : f.modules ⋙ sections R ⟶ sections S := {
    app := fun M ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk' (sectionsEquiv f M)
      (sectionsEquiv_add f M))
    naturality := by
      intro M N v
      ext x
      exact sectionsEquiv_naturality f v x }
  have : ∀ M, IsIso (c.app M) := fun M ↦
    (ConcreteCategory.isIso_iff_bijective (c.app M)).mpr (sectionsEquiv f M).bijective
  have : IsIso c := NatIso.isIso_of_isIso_app c
  exact ⟨asIso c, sectionsEquiv_spec f⟩

attribute [local irreducible] towerDerivedEvaluationTransition

@[irreducible] private def unitNatModel {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  let q := HomotopyCategory.quotient A (.up ℤ)
  let e := Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _
  e.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      F.rightDerivedFunctor).hom


private theorem unitNatModel_app {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (I : CochainComplex A ℤ) : (unitNatModel F).app I = unit F I := by
  simp [unitNatModel, unit, UnboundedExactTower.cochainUnit, Category.assoc]


@[irreducible] private def unitNat {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app I := unit F I
  naturality I T f := by
    simpa only [Functor.comp_map, unitNatModel_app] using (unitNatModel F).naturality f

private theorem unitNat_app {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (I : CochainComplex A ℤ) : (unitNat F).app I = unit F I := by
  unfold unitNat
  rfl

private instance unit_isIso {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (unit F I) := by
  unfold unit UnboundedExactTower.cochainUnit
  infer_instance

private instance unitNat_universal {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    F.rightDerivedFunctor.IsRightDerivedFunctor (unitNat F)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  apply (derives F).isRightDerivedFunctor_of_isIso
  intro I
  have := I.property
  rw [show (CochainComplex.KInjectives.localizerMorphism A).functor.obj I = I.obj from rfl,
    unitNat_app]
  infer_instance

private theorem unit_naturality {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    {I T : CochainComplex A ℤ} (v : I ⟶ T) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map v) ≫ unit F T =
      unit F I ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map v) :=
  by simpa only [Functor.comp_map, unitNat_app] using (unitNat F).naturality v

@[irreducible] private def restrictionNat
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] {E : Type e} [Category.{ev} E] [Abelian E]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H') :
    H ⟶ F ⋙ H' :=
  (Functor.leftUnitor H).inv ≫ Functor.whiskerRight adj.unit H ≫
    (Functor.associator F G H).hom ≫ Functor.whiskerLeft F c.hom

private theorem restrictionMap_eq
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] {E : Type e} [Category.{ev} E] [Abelian E]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (I : CochainComplex A ℤ) (T : CochainComplex B ℤ)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ T) :
    restrictionMap F G adj H H' c I T v =
      (NatTrans.mapHomologicalComplex (restrictionNat F G adj H H' c) (.up ℤ)).app I ≫
        (H'.mapHomologicalComplex (.up ℤ)).map v := by
  ext i
  simp only [restrictionMap, restrictionNat, Adjunction.homEquiv_unit,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Functor.map_comp,
    Adjunction.mapHomologicalComplex_unit_app_f, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.assoc]
  exact congrArg (fun k ↦ H.map (adj.unit.app (I.X i)) ≫ k)
    (c.hom.naturality (v.f i))

private def RestrictionUnit
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] {E : Type e} [Category.{ev} E] [Abelian E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (rho : H.rightDerivedFunctor ⟶ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor) : Prop :=
  ∀ (I : CochainComplex A ℤ) (T : CochainComplex B ℤ)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ T),
      unit H I ≫ rho.app (DerivedCategory.Q.obj I) ≫
          H'.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app I) ≫
          H'.rightDerivedFunctor.map (DerivedCategory.Q.map v) =
        DerivedCategory.Q.map (restrictionMap F G adj H H' c I T v) ≫ unit H' T

private theorem restriction_exists
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] {E : Type e} [Category.{ev} E] [Abelian E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H') :
    ∃ rho : H.rightDerivedFunctor ⟶ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor,
      RestrictionUnit F G adj H H' c rho := by
  let β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ H'.rightDerivedFunctor) :=
    Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (restrictionNat F G adj H H' c) (.up ℤ))
        DerivedCategory.Q ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (unitNat H') ≫
      Functor.whiskerRight F.mapDerivedCategoryFactors.inv H'.rightDerivedFunctor
  let rho := H.rightDerivedFunctor.rightDerivedDesc (unitNat H)
    (HomologicalComplex.quasiIso A (.up ℤ)) _ β
  refine ⟨rho, ?_⟩
  intro I T v
  have h := Functor.rightDerived_fac_app H.rightDerivedFunctor (unitNat H)
    (HomologicalComplex.quasiIso A (.up ℤ)) _ β I
  rw [unitNat_app] at h
  change unit H I ≫ rho.app (DerivedCategory.Q.obj I) = _ at h
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [β, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, unitNat_app, Category.assoc]
  try simp only [Functor.map_comp, Category.assoc]
  with_unfolding_all rw [← H'.rightDerivedFunctor.map_comp_assoc, Iso.inv_hom_id_app,
    H'.rightDerivedFunctor.map_id, Category.id_comp]
  erw [← unit_naturality]
  rw [restrictionMap_eq, DerivedCategory.Q.map_comp, Category.assoc]

private def towerIso {A : Type a} {B : Type b} {E : Type e}
    [Category.{v} A] [Category.{z} B] [Category.{ev} E]
    {G : B ⥤ A} {H : A ⥤ E} {H' : B ⥤ E} (c : G ⋙ H ≅ H') :
    tower G ⋙ tower H ≅ tower H' :=
  NatIso.ofComponents (fun T ↦
    NatIso.ofComponents (fun n ↦ c.app (T.obj n)) (fun t ↦ c.hom.naturality (T.map t)))
    (fun t ↦ by apply NatTrans.ext; funext n; exact c.hom.naturality (t.app n))

private theorem restriction_limit_projection
    {A : Type a} {B : Type b} {E : Type e}
    [Category.{v} A] [Category.{z} B] [Category.{ev} E]
    (F : A ⥤ B) (G : B ⥤ A) (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) (c : G ⋙ H ≅ H')
    (I : ℕᵒᵖ ⥤ A) (T : ℕᵒᵖ ⥤ B) (v : I ⋙ F ⟶ T)
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasLimitsOfShape ℕᵒᵖ E]
    [HasLimit I] [HasLimit T] [HasLimit (I ⋙ F)] [HasLimit (I ⋙ H)]
    [HasLimit (T ⋙ H')] (n : ℕᵒᵖ) :
    H.map (adj.unit.app (limit I)) ≫
      H.map (G.map (limit.post I F)) ≫ H.map (G.map (lim.map v)) ≫
      c.hom.app (limit T) ≫ limit.post T H' ≫
      limit.π (T ⋙ H') n =
    limit.post I H ≫
      lim.map (Functor.whiskerRight ((adj.whiskerRight ℕᵒᵖ).unit.app I) H) ≫
      lim.map (Functor.whiskerRight (Functor.whiskerRight v G) H) ≫
      lim.map (NatIso.ofComponents (fun n ↦ c.app (T.obj n))
        (fun t ↦ c.hom.naturality (T.map t))).hom ≫
      limit.π (T ⋙ H') n := by
  with_unfolding_all simp only [← limMap_eq, limMap_π, limMap_π_assoc, limit.post_π,
    limit.post_π_assoc]
  simp only [Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
    Adjunction.whiskerRight_unit_app_app]
  erw [← c.hom.naturality]
  simp only [Functor.comp_map]
  have hv : H.map (G.map (limMap v)) ≫ H.map (G.map (limit.π T n)) =
      H.map (G.map (limit.π (I ⋙ F) n)) ≫ H.map (G.map (v.app n)) := by
    rw [← H.map_comp, ← G.map_comp, limMap_π, G.map_comp, H.map_comp]
  rw [reassoc_of% hv]
  have hp : H.map (G.map (limit.post I F)) ≫
      H.map (G.map (limit.π (I ⋙ F) n)) =
      H.map (G.map (F.map (limit.π I n))) := by
    rw [← H.map_comp, ← G.map_comp, limit.post_π]
  rw [reassoc_of% hp]
  have hu : H.map (adj.unit.app (limit I)) ≫
      H.map (G.map (F.map (limit.π I n))) =
      H.map (limit.π I n) ≫ H.map (adj.unit.app (I.obj n)) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (adj.unit.naturality (limit.π I n)).symm
  rw [reassoc_of% hu]
  rfl

private theorem restrictionMap_limit
    {A : Type a} {B : Type b} {E : Type e}
    [Category.{v} A] [Category.{z} B] [Category.{ev} E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ E]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (T : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (v : ((tower F).mapHomologicalComplex (.up ℤ)).obj I ⟶ T) :
    restrictionMap F G adj H H' c
        (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I)
        (((limitFunctor B).mapHomologicalComplex (.up ℤ)).obj T)
        (limitMap F I ≫ ((limitFunctor B).mapHomologicalComplex (.up ℤ)).map v) ≫
      limitMap H' T =
    limitMap H I ≫ ((limitFunctor E).mapHomologicalComplex (.up ℤ)).map
      (restrictionMap (tower F) (tower G) (adj.whiskerRight ℕᵒᵖ)
        (tower H) (tower H') (towerIso c) I T v) := by
  ext i
  apply limit.hom_ext
  intro n
  simp only [restrictionMap, Adjunction.homEquiv_unit, Functor.map_comp,
    HomologicalComplex.comp_f, limitMap, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f,
    Category.assoc]
  exact restriction_limit_projection F G adj H H' c (I.X i) (T.X i) (v.f i) n

private theorem transition_id {A : Type a} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] (n : ℕᵒᵖ) :
    towerDerivedEvaluationTransition A (𝟙 n) = 𝟙 (evaluate n) := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
  intro X
  apply (cancel_mono (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app X)).mp
  rw [towerTransition_fac]
  have h : ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map (𝟙 n))
      (.up ℤ)).app X) = 𝟙 _ := by
    rw [Functor.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  rw [h, DerivedCategory.Q.map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  with_unfolding_all exact Category.comp_id _

private theorem transition_comp {A : Type a} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {n m k : ℕᵒᵖ} (t : n ⟶ m) (s : m ⟶ k) :
    towerDerivedEvaluationTransition A (t ≫ s) =
      towerDerivedEvaluationTransition A t ≫ towerDerivedEvaluationTransition A s := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
  intro X
  apply (cancel_mono (((evaluation ℕᵒᵖ A).obj k).mapDerivedCategoryFactors.hom.app X)).mp
  simp only [NatTrans.comp_app, Category.assoc, towerTransition_fac]
  rw [← Category.assoc, towerTransition_fac, Category.assoc, ← Functor.map_comp]
  congr 2
  ext i
  exact (X.X i).map_comp t s

private def evaluationTower (A : Type a) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] :
    DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A) where
  obj M := {
    obj := fun n ↦ (evaluate n).obj M
    map := fun t ↦ (towerDerivedEvaluationTransition A t).app M
    map_id := fun n ↦ congrArg (fun t ↦ t.app M) (transition_id n)
    map_comp := fun t s ↦ congrArg (fun t ↦ t.app M) (transition_comp t s) }
  map f := {
    app := fun n ↦ (evaluate n).map f
    naturality := fun _ _ t ↦ (towerDerivedEvaluationTransition A t).naturality f |>.symm }

private def evaluationTowerFactors (A : Type a) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] :
    DerivedCategory.Q ⋙ evaluationTower A ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
          (DerivedCategory.{w} A)).obj DerivedCategory.Q :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun n ↦ ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.app X)
    (fun t ↦ towerTransition_fac A t X)) (fun f ↦ by
      ext n
      exact (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.naturality f))

private theorem evaluationComparison_exists
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (F : A ⥤ B) [F.Additive] :
    ∃ e : ∀ n : ℕᵒᵖ, (tower F).rightDerivedFunctor ⋙ evaluate n ≅
      evaluate n ⋙ F.rightDerivedFunctor, IsEvaluationComparison F e := by
  obtain ⟨e, he⟩ := towerComparison_existsEvaluationIso F F.rightDerivedFunctor
    (tower F).rightDerivedFunctor (unitNat F) (unitNat (tower F))
    (fun I hI ↦ by have := hI; rw [unitNat_app]; infer_instance)
    (fun I hI ↦ by have := hI; rw [unitNat_app]; infer_instance)
    (evaluationTower A) (evaluationTower B) (evaluationTowerFactors A)
    (evaluationTowerFactors B)
  let e' (n : ℕᵒᵖ) : (tower F).rightDerivedFunctor ⋙ evaluate n ≅
      evaluate n ⋙ F.rightDerivedFunctor :=
    NatIso.ofComponents (fun M ↦ (e.app M).app n) (fun f ↦ by
      exact congrArg (fun t ↦ t.app n) (e.hom.naturality f))
  refine ⟨e', ?_, ?_⟩
  · intro I n
    simpa only [unitNat_app, evaluationTower, evaluationTowerFactors, e',
      Functor.comp_obj, Functor.comp_map, NatIso.ofComponents_hom_app,
      NatTrans.comp_app, Iso.app_hom] using he I n
  · intro M n m t
    exact (e.hom.app M).naturality t

private theorem splitRoosComparisonQuasiIso
    {B : Type b} [Category.{z} B] [Abelian B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} B]
    (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    [∀ (p : ℤ) (n : ℕ), IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op)] :
    QuasiIso (ExactProductsRoos.comparison.app I) := by
  obtain ⟨h, hs⟩ := SheafOfModules.sectionsSplitRoos I
  let S := ShortComplex.mk (ExactProductsRoos.inclusion.app I)
    (-ExactProductsRoos.difference.app I)
    (by rw [Preadditive.comp_neg, ExactProductsRoos.inclusion_difference, neg_zero])
  have hS : S.ShortExact := by
    apply ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk _ _ h) _ hs
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp } (by simp [S]) (by
          change 𝟙 _ ≫ (-ExactProductsRoos.difference.app I) = _ ≫ (-𝟙 _)
          simp)
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hS
    (ExactProductsRoos.comparison_condition I)

private theorem imageLimitAcyclic
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    {B : Type b} [Category.{z} B] [Abelian B] [IsGrothendieckAbelian.{z} B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (H : A ⥤ B) [H.Additive]
    (L : SheafOfModules.SequenceSectionsDerivedPair
      (limitFunctor B))
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
    IsIso (L.unit.app (((tower H).mapHomologicalComplex (.up ℤ)).obj I)) := by
  have : IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A) := SheafOfModules.sectionsTowerGrothendieck
  have : IsGrothendieckAbelian.{z} (ℕᵒᵖ ⥤ B) :=
    SheafOfModules.sectionsTowerGrothendieck
  have := hI
  let W := (Functor.whiskeringRight ℕᵒᵖ A B).obj H
  let J := (CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)).obj I
  let q : I ⟶ J := (CochainComplex.toKInjectiveResolution.{v} (ℕᵒᵖ ⥤ A)).app I
  have : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff q).mp inferInstance
  have hWq : QuasiIso ((W.mapHomologicalComplex (.up ℤ)).map q) := by
    rw [← he]
    exact (W.mapHomotopyEquiv e).quasiIso_hom
  have hLq : QuasiIso
      ((lim.mapHomologicalComplex (.up ℤ)).map ((W.mapHomologicalComplex (.up ℤ)).map q)) := by
    rw [← he]
    exact (lim.mapHomotopyEquiv (W.mapHomotopyEquiv e)).quasiIso_hom
  have (p : ℤ) (n : ℕ) : IsSplitEpi
      ((((W.mapHomologicalComplex (.up ℤ)).obj J).X p).map
        (homOfLE (Nat.le_succ n)).op) := by
    have := CategoryTheory.injective_tower_transition_split (J.X p) n
    change IsSplitEpi (H.map ((J.X p).map (homOfLE (Nat.le_succ n)).op))
    infer_instance
  have : QuasiIso (ExactProductsRoos.comparison.app
      ((W.mapHomologicalComplex (.up ℤ)).obj J)) := splitRoosComparisonQuasiIso _
  obtain ⟨a, ha⟩ := ExactProductsRoos.comparisonIso L.functor L.unit L.computes
  have hη : IsIso (L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj J)) := by
    have heq := congrArg (fun η ↦ η.app ((W.mapHomologicalComplex (.up ℤ)).obj J)) ha
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at heq
    rw [← heq]
    infer_instance
  have hn := L.unit.naturality ((W.mapHomologicalComplex (.up ℤ)).map q)
  have : IsIso (L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q))) := by
    change _ = L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q)) at hn
    rw [← hn]
    change IsIso (DerivedCategory.Q.map
      ((lim.mapHomologicalComplex (.up ℤ)).map
        ((W.mapHomologicalComplex (.up ℤ)).map q)) ≫
      L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj J))
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q)))

private instance sections_preservesLimits {C : Type u} [SmallCategory C] [HasTerminal C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (sections R) := by
  have := towerComparison_underlyingPreservesLimits R
  have : PreservesLimitsOfShape ℕᵒᵖ ((sections R) ⋙ forget AddCommGrpCat.{u}) := by
    change PreservesLimitsOfShape ℕᵒᵖ
      ((SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)) ⋙
        sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj (op (⊤_ C)))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (sections R)
    (forget AddCommGrpCat.{u})

private theorem limitComparison_exists
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasLimitsOfShape ℕᵒᵖ AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (H : A ⥤ AddCommGrpCat.{u}) [H.Additive] [PreservesLimitsOfShape ℕᵒᵖ H] :
    ∃ a : (limitFunctor A).rightDerivedFunctor ⋙ H.rightDerivedFunctor ≅
      (tower H).rightDerivedFunctor ⋙ (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor,
      IsLimitComparison H a := by
  let L : SheafOfModules.SequenceSectionsDerivedPair (limitFunctor AddCommGrpCat.{u}) :=
    ⟨_, unitNat _, inferInstance, fun I hI ↦ by
      have := hI
      rw [unitNat_app]
      change IsIso (unit (limitFunctor AddCommGrpCat.{u}) I)
      infer_instance⟩
  obtain ⟨a, ha⟩ := towerComparison_existsLimitIso H H.rightDerivedFunctor
    (tower H).rightDerivedFunctor (limitFunctor A).rightDerivedFunctor
    (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor
    (unitNat H) (unitNat (tower H)) (unitNat (limitFunctor A))
    (unitNat (limitFunctor AddCommGrpCat.{u}))
    (fun I hI ↦ by have := hI; rw [unitNat_app]; infer_instance)
    (fun I hI ↦ by have := hI; rw [unitNat_app]; infer_instance)
    (fun I hI ↦ by have := hI; rw [unitNat_app]; infer_instance)
    (fun I hI ↦ imageLimitAcyclic H L I hI)
    (preservesLimitNatIso H (J := ℕᵒᵖ))
  refine ⟨a, ?_⟩
  intro I
  have hmap : (NatTrans.mapHomologicalComplex
      (preservesLimitNatIso H (J := ℕᵒᵖ)).hom (.up ℤ)).app I = limitMap H I := by
    ext i
    rfl
  simpa only [unitNat_app, hmap] using ha I

private def InverseLimitUnit
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B] [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (lambda : (limitFunctor A).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      (tower F).mapDerivedCategory ⋙ (limitFunctor B).rightDerivedFunctor) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (T : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (v : ((tower F).mapHomologicalComplex (.up ℤ)).obj I ⟶ T),
      F.mapDerivedCategory.map (unit (limitFunctor A) I) ≫
          lambda.hom.app (DerivedCategory.Q.obj I) ≫
          (limitFunctor B).rightDerivedFunctor.map
            ((tower F).mapDerivedCategoryFactors.hom.app I) ≫
          (limitFunctor B).rightDerivedFunctor.map (DerivedCategory.Q.map v) =
        F.mapDerivedCategoryFactors.hom.app
            (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map (limitMap F I ≫
            ((limitFunctor B).mapHomologicalComplex (.up ℤ)).map v) ≫
          unit (limitFunctor B) T

private theorem inverseLimitComparison_exists
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{v} A] [IsGrothendieckAbelian.{z} B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasLimitsOfShape ℕᵒᵖ A]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F] :
    ∃ lambda : (limitFunctor A).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      (tower F).mapDerivedCategory ⋙ (limitFunctor B).rightDerivedFunctor,
      InverseLimitUnit F lambda := by
  let L : SheafOfModules.SequenceSectionsDerivedPair (limitFunctor B) :=
    ⟨_, unitNat _, inferInstance, fun I hI ↦ by
      have := hI
      rw [unitNat_app]
      infer_instance⟩
  obtain ⟨lambda, hl⟩ := towerComparison_existsLimitIso F F.mapDerivedCategory
    (tower F).mapDerivedCategory (limitFunctor A).rightDerivedFunctor
    (limitFunctor B).rightDerivedFunctor F.mapDerivedCategoryFactors.inv
    (tower F).mapDerivedCategoryFactors.inv (unitNat (limitFunctor A))
    (unitNat (limitFunctor B))
    (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
    (fun I hI ↦ by have := hI; rw [unitNat_app]; infer_instance)
    (fun I hI ↦ imageLimitAcyclic F L I hI) (preservesLimitNatIso F (J := ℕᵒᵖ))
  refine ⟨lambda, ?_⟩
  intro I T v
  have h := hl I
  have hm : (NatTrans.mapHomologicalComplex (preservesLimitNatIso F (J := ℕᵒᵖ)).hom
      (.up ℤ)).app I = limitMap F I := by ext i; rfl
  simp only [unitNat_app, hm] at h
  apply (cancel_epi (F.mapDerivedCategoryFactors.inv.app
    (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I))).mp
  simp only [← Category.assoc]
  simp only [Category.assoc] at *
  with_unfolding_all rw [reassoc_of% h]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  have hn := unit_naturality (limitFunctor B) v
  have he := congrArg (fun f ↦ DerivedCategory.Q.map (limitMap F I) ≫ f) hn.symm
  with_unfolding_all simpa only [Category.assoc, Functor.map_comp] using he

private theorem restrictionMap_evaluate
    {A : Type a} {B : Type b} {E : Type e}
    [Category.{v} A] [Category.{z} B] [Category.{ev} E]
    [Abelian A] [Abelian B] [Abelian E]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) :
    (((evaluation ℕᵒᵖ E).obj n).mapHomologicalComplex (.up ℤ)).map
      (restrictionMap (tower F) (tower G) (adj.whiskerRight ℕᵒᵖ)
        (tower H) (tower H') (towerIso c) I
        (((tower F).mapHomologicalComplex (.up ℤ)).obj I) (𝟙 _)) =
    restrictionMap F G adj H H' c (I.asFunctor.obj n)
      ((F.mapHomologicalComplex (.up ℤ)).obj (I.asFunctor.obj n)) (𝟙 _) := by
  ext p
  simp [restrictionMap, Adjunction.homEquiv_unit,
    Adjunction.mapHomologicalComplex_unit_app_f, tower, towerIso,
    Adjunction.whiskerRight_unit_app_app, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex]

private theorem evaluation_restriction_coherence
    {A : Type a} {B : Type b} {E : Type e}
    [Category.{v} A] [Category.{z} B] [Category.{ev} E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (rho : H.rightDerivedFunctor ⟶ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor)
    (rhoT : (tower H).rightDerivedFunctor ⟶
      (tower F).mapDerivedCategory ⋙ (tower H').rightDerivedFunctor)
    (eR : ∀ n, (tower H).rightDerivedFunctor ⋙ evaluate n ≅
      evaluate n ⋙ H.rightDerivedFunctor)
    (eS : ∀ n, (tower H').rightDerivedFunctor ⋙ evaluate n ≅
      evaluate n ⋙ H'.rightDerivedFunctor)
    (hr : RestrictionUnit F G adj H H' c rho)
    (hrt : RestrictionUnit (tower F) (tower G) (adj.whiskerRight ℕᵒᵖ)
      (tower H) (tower H') (towerIso c) rhoT)
    (heR : IsEvaluationComparison H eR) (heS : IsEvaluationComparison H' eS) :
    ∀ (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (n : ℕᵒᵖ),
      (evaluate n).map (rhoT.app M) ≫
        (eS n).hom.app ((tower F).mapDerivedCategory.obj M) ≫
        H'.rightDerivedFunctor.map ((towerDerivedEvaluationInterchange F n).hom.app M) =
      (eR n).hom.app M ≫ rho.app ((evaluate n).obj M) := by
  intro M n
  let l : (tower H).rightDerivedFunctor ⋙ evaluate n ⟶
      evaluate n ⋙ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor :=
    Functor.whiskerRight rhoT (evaluate n) ≫
      Functor.whiskerLeft (tower F).mapDerivedCategory (eS n).hom ≫
      Functor.whiskerRight (towerDerivedEvaluationInterchange F n).hom H'.rightDerivedFunctor
  let r : (tower H).rightDerivedFunctor ⋙ evaluate n ⟶
      evaluate n ⋙ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor :=
    (eR n).hom ≫ Functor.whiskerLeft (evaluate n) rho
  suffices l = r from NatTrans.congr_app this M
  apply SheafOfModules.sectionsNatTransExt
  intro I hI
  have := hI
  apply (cancel_epi ((evaluate n).map (unit (tower H) I))).mp
  apply (cancel_mono (H'.rightDerivedFunctor.map
    (F.mapDerivedCategory.map
        (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app I) ≫
      F.mapDerivedCategoryFactors.hom.app (I.asFunctor.obj n)))).mp
  try dsimp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.comp_obj, Functor.map_comp, Category.assoc]
  have hi := towerInterchange_fac F n I
  have hrtI := hrt I (((tower F).mapHomologicalComplex (.up ℤ)).obj I) (𝟙 _)
  have hrI := hr (I.asFunctor.obj n)
    ((F.mapHomologicalComplex (.up ℤ)).obj (I.asFunctor.obj n)) (𝟙 _)
  simp only [Functor.map_id] at hrtI hrI
  with_unfolding_all erw [Functor.map_id, Category.comp_id] at hrtI hrI
  with_unfolding_all erw [← H'.rightDerivedFunctor.map_comp_assoc,
    ← H'.rightDerivedFunctor.map_comp]
  simp only [Category.assoc]
  with_unfolding_all erw [hi]
  simp only [Functor.map_comp]
  erw [← (eS n).hom.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← (evaluate n).map_comp_assoc, ← (evaluate n).map_comp_assoc]
  with_unfolding_all erw [Category.assoc, hrtI]
  simp only [Functor.map_comp]
  try with_unfolding_all simp only [Category.assoc]
  with_unfolding_all erw [heS.1 (((tower F).mapHomologicalComplex (.up ℤ)).obj I) n]
  with_unfolding_all erw [← rho.naturality_assoc]
  try with_unfolding_all simp only [Functor.comp_map, Category.assoc]
  with_unfolding_all erw [reassoc_of% heR.1 I n, hrI]
  with_unfolding_all erw [(((evaluation ℕᵒᵖ E).obj n).mapDerivedCategoryFactors.hom.naturality_assoc
    (restrictionMap (tower F) (tower G) (adj.whiskerRight ℕᵒᵖ)
      (tower H) (tower H') (towerIso c) I
      (((tower F).mapHomologicalComplex (.up ℤ)).obj I) (𝟙 _)))]
  simp only [Functor.comp_map]
  with_unfolding_all rw [restrictionMap_evaluate]
  with_unfolding_all rfl

private theorem limit_restriction_coherence
    {A : Type a} {B : Type b} {E : Type e}
    [Category.{v} A] [Category.{z} B] [Category.{ev} E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions E]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive] (c : G ⋙ H ≅ H')
    (rho : H.rightDerivedFunctor ⟶ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor)
    (rhoT : (tower H).rightDerivedFunctor ⟶
      (tower F).mapDerivedCategory ⋙ (tower H').rightDerivedFunctor)
    (lambda : (limitFunctor A).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      (tower F).mapDerivedCategory ⋙ (limitFunctor B).rightDerivedFunctor)
    (aR : (limitFunctor A).rightDerivedFunctor ⋙ H.rightDerivedFunctor ≅
      (tower H).rightDerivedFunctor ⋙ (limitFunctor E).rightDerivedFunctor)
    (aS : (limitFunctor B).rightDerivedFunctor ⋙ H'.rightDerivedFunctor ≅
      (tower H').rightDerivedFunctor ⋙ (limitFunctor E).rightDerivedFunctor)
    (hr : RestrictionUnit F G adj H H' c rho)
    (hrt : RestrictionUnit (tower F) (tower G) (adj.whiskerRight ℕᵒᵖ)
      (tower H) (tower H') (towerIso c) rhoT)
    (hl : InverseLimitUnit F lambda)
    (haR : IsLimitComparison H aR) (haS : IsLimitComparison H' aS) :
    ∀ M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
      rho.app ((limitFunctor A).rightDerivedFunctor.obj M) ≫
        H'.rightDerivedFunctor.map (lambda.hom.app M) ≫
        aS.hom.app ((tower F).mapDerivedCategory.obj M) =
      aR.hom.app M ≫ (limitFunctor E).rightDerivedFunctor.map (rhoT.app M) := by
  let l : (limitFunctor A).rightDerivedFunctor ⋙ H.rightDerivedFunctor ⟶
      (tower F).mapDerivedCategory ⋙ (tower H').rightDerivedFunctor ⋙
        (limitFunctor E).rightDerivedFunctor :=
    Functor.whiskerLeft (limitFunctor A).rightDerivedFunctor rho ≫
      Functor.whiskerRight lambda.hom H'.rightDerivedFunctor ≫
      Functor.whiskerLeft (tower F).mapDerivedCategory aS.hom
  let r : (limitFunctor A).rightDerivedFunctor ⋙ H.rightDerivedFunctor ⟶
      (tower F).mapDerivedCategory ⋙ (tower H').rightDerivedFunctor ⋙
        (limitFunctor E).rightDerivedFunctor :=
    aR.hom ≫ Functor.whiskerRight rhoT (limitFunctor E).rightDerivedFunctor
  suffices l = r from fun M ↦ NatTrans.congr_app this M
  apply SheafOfModules.sectionsNatTransExt
  intro I hI
  have := hI
  have : (limitFunctor A).PreservesKInjectiveComplexes :=
    towerComparison_limPreservesKInjective (A := A)
  apply (cancel_epi (unit H (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I) ≫
    H.rightDerivedFunctor.map (unit (limitFunctor A) I))).mp
  apply (cancel_mono ((limitFunctor E).rightDerivedFunctor.map
    ((tower H').rightDerivedFunctor.map ((tower F).mapDerivedCategoryFactors.hom.app I)))).mp
  try dsimp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  try simp only [Functor.comp_obj, Category.assoc]
  erw [← aS.hom.naturality, ← H'.rightDerivedFunctor.map_comp_assoc]
  erw [reassoc_of% rho.naturality]
  try simp only [Functor.comp_map, Category.assoc]
  have hli := hl I (((tower F).mapHomologicalComplex (.up ℤ)).obj I) (𝟙 _)
  simp only [Functor.map_id] at hli
  with_unfolding_all erw [Functor.map_id, Category.comp_id] at hli
  have hri := hr (((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj I)
    (((limitFunctor B).mapHomologicalComplex (.up ℤ)).obj
      (((tower F).mapHomologicalComplex (.up ℤ)).obj I)) (limitMap F I)
  have hrti := hrt I (((tower F).mapHomologicalComplex (.up ℤ)).obj I) (𝟙 _)
  simp only [Functor.map_id] at hrti
  with_unfolding_all erw [Functor.map_id, Category.comp_id] at hrti
  try simp only [Functor.map_comp, Category.assoc] at hli
  repeat' erw [Functor.map_id] at hli
  repeat' erw [Category.id_comp] at hli
  with_unfolding_all erw [← H'.rightDerivedFunctor.map_comp_assoc, hli]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hri]
  try simp only [Functor.comp_map, Category.assoc]
  with_unfolding_all erw [haS (((tower F).mapHomologicalComplex (.up ℤ)).obj I),
    reassoc_of% haR I]
  simp only [← Functor.map_comp]
  erw [hrti]
  simp only [Functor.map_comp]
  erw [← reassoc_of% unit_naturality]
  try simp only [← Functor.map_comp, Category.assoc]
  have h := restrictionMap_limit F G adj H H' c I
    (((tower F).mapHomologicalComplex (.up ℤ)).obj I) (𝟙 _)
  with_unfolding_all simp only [Functor.map_id, Category.comp_id] at h
  with_unfolding_all erw [← DerivedCategory.Q.map_comp_assoc,
    ← DerivedCategory.Q.map_comp_assoc, h]


attribute [local irreducible] ordinaryLimitIso

@[irreducible] private def ordinaryUnit {A : Type a} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (limitFunctor A).rightDerivedFunctor :=
  (Functor.isoWhiskerRight (ordinaryLimitIso (A := A)).symm DerivedCategory.Q).hom ≫
    unitNat (limitFunctor A)

private instance ordinaryUnit_universal {A : Type a} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] :
    (limitFunctor A).rightDerivedFunctor.IsRightDerivedFunctor (ordinaryUnit (A := A))
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  have h := Functor.IsRightDerivedFunctor.isLeftKanExtension
    (limitFunctor A).rightDerivedFunctor (unitNat (limitFunctor A))
    (HomologicalComplex.quasiIso _ (.up ℤ))
  apply (Functor.isLeftKanExtension_iff_of_iso₂ (unitNat (limitFunctor A))
    (ordinaryUnit (A := A))
    (Functor.isoWhiskerRight (ordinaryLimitIso (A := A)) DerivedCategory.Q)
    (Iso.refl _) ?_).mp h
  unfold ordinaryUnit
  change unitNat (limitFunctor A) ≫ Functor.whiskerLeft DerivedCategory.Q (𝟙 _) =
    (Functor.isoWhiskerRight (ordinaryLimitIso (A := A)) DerivedCategory.Q).hom ≫
      ((Functor.isoWhiskerRight (ordinaryLimitIso (A := A)) DerivedCategory.Q).inv ≫
        unitNat (limitFunctor A))
  rw [Functor.whiskerLeft_id', Category.comp_id, Iso.hom_inv_id_assoc]

private theorem inclusion_eq {A : Type a} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    limitInclusion I = (ordinaryLimitIso (A := A)).hom.app I ≫ roosι I := by
  unfold limitInclusion
  rw [roosAugment_eq]
  suffices roosAugmentLimit
      (fun n ↦ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) _ =
      (ordinaryLimitIso (A := A)).hom.app I by rw [this]
  apply limit.hom_ext
  intro n
  have hp : (ordinaryLimitIso (A := A)).hom.app I ≫ limit.π I.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I := by
    ext i
    with_unfolding_all exact HomologicalComplex.limitXIso_hom_π_f I.asFunctor i n
  rw [hp]
  exact roosAugmentLimit_π _ _ n.unop

@[irreducible] private def augmentationLimit {A : Type a} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hgamma : ∀ n, gamma (n + 1) ≫
      X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) :
    P ⟶ ((limitFunctor A).mapHomologicalComplex (.up ℤ)).obj X :=
  roosAugmentLimit gamma hgamma ≫ (ordinaryLimitIso (A := A)).inv.app X

private theorem augmentationLimit_factor {A : Type a} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hgamma : ∀ n, gamma (n + 1) ≫
      X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) :
    roosAugment gamma hgamma = augmentationLimit gamma hgamma ≫ limitInclusion X := by
  rw [inclusion_eq]
  simp only [augmentationLimit, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact roosAugment_eq gamma hgamma

private theorem augmentationLimit_projection {A : Type a} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hgamma : ∀ n, gamma (n + 1) ≫
      X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) (n : ℕ) :
    augmentationLimit gamma hgamma ≫
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X = gamma n := by
  have hp : (ordinaryLimitIso (A := A)).hom.app X ≫ limit.π X.asFunctor (op n) =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X := by
    ext i
    with_unfolding_all exact HomologicalComplex.limitXIso_hom_π_f X.asFunctor i (op n)
  rw [augmentationLimit, Category.assoc, ← hp, Iso.inv_hom_id_app_assoc]
  exact roosAugmentLimit_π gamma hgamma n

private theorem augmentationLimit_map {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive]
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hgamma : ∀ n, gamma (n + 1) ≫
      X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) :
    (F.mapHomologicalComplex (.up ℤ)).map (augmentationLimit gamma hgamma) ≫
      limitMap F X =
    augmentationLimit
      (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
      (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n))
      (fun n ↦ by
        change (F.mapHomologicalComplex (.up ℤ)).map (gamma (n + 1)) ≫
          (F.mapHomologicalComplex (.up ℤ)).map
            (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
        rw [← Functor.map_comp, hgamma]) := by
  ext i
  apply limit.hom_ext
  intro n
  let k := n.unop
  change _ ≫ limit.π _ (op k) = _
  have h₁ := congrArg (fun f ↦ f.f i) (augmentationLimit_projection gamma hgamma k)
  have h₂ := congrArg (fun f ↦ f.f i)
    (augmentationLimit_projection
      (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
      (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n))
      (fun n ↦ by
        change (F.mapHomologicalComplex (.up ℤ)).map (gamma (n + 1)) ≫
          (F.mapHomologicalComplex (.up ℤ)).map
            (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
        rw [← Functor.map_comp, hgamma]) k)
  with_unfolding_all
    change (F.map ((augmentationLimit gamma hgamma).f i) ≫ limit.post (X.X i) F) ≫
      limit.π (X.X i ⋙ F) (op k) = _
  rw [Category.assoc]
  rw [limit.post_π, ← F.map_comp]
  exact (congrArg F.map h₁).trans h₂.symm

private theorem augmentation_unit_comparison {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (lambda : (limitFunctor A).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      (tower F).mapDerivedCategory ⋙ (limitFunctor B).rightDerivedFunctor)
    (hl : InverseLimitUnit F lambda)
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hgamma : ∀ n, gamma (n + 1) ≫
      X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) :
    F.mapDerivedCategory.map
        (DerivedCategory.Q.map (augmentationLimit gamma hgamma) ≫
          unit (limitFunctor A) X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (augmentationLimit
          (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
          (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n))
          (fun n ↦ by
            change (F.mapHomologicalComplex (.up ℤ)).map (gamma (n + 1)) ≫
              (F.mapHomologicalComplex (.up ℤ)).map
                (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
            rw [← Functor.map_comp, hgamma])) ≫
        unit (limitFunctor B) (((tower F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        (limitFunctor B).rightDerivedFunctor.map ((tower F).mapDerivedCategoryFactors.inv.app X)
      := by
  apply (cancel_mono ((limitFunctor B).rightDerivedFunctor.map
    ((tower F).mapDerivedCategoryFactors.hom.app X))).mp
  have h := hl X (((tower F).mapHomologicalComplex (.up ℤ)).obj X) (𝟙 _)
  repeat' erw [Functor.map_id] at h
  repeat' erw [Category.comp_id] at h
  simp only [Functor.map_comp, Category.assoc]
  with_unfolding_all erw [h]
  erw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc, augmentationLimit_map]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  with_unfolding_all erw [Functor.map_id, Category.comp_id]

private theorem roosComparison_of_derived {A : Type a} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (κ : roosF (A := A) ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    [CF.IsRightDerivedFunctor (roosDerivedUnit κ)
      (HomologicalComplex.quasiIso _ (.up ℤ))] :
    ∃ theta : roosF (A := A) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor A).rightDerivedFunctor,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        DerivedCategory.Q.{w}.map (limitInclusion I) ≫ theta.hom.app I =
        unit (limitFunctor A) I := by
  let η := ordinaryUnit (A := A)
  let e := Functor.rightDerivedUnique CF
    (limitFunctor (A)).rightDerivedFunctor
    (roosDerivedUnit κ) η (HomologicalComplex.quasiIso _ (.up ℤ))
  let theta := κ ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q e
  refine ⟨theta, ?_⟩
  intro I
  have h := Functor.rightDerivedNatTrans_app CF
    (limitFunctor (A)).rightDerivedFunctor
    (roosDerivedUnit κ) η (HomologicalComplex.quasiIso _ (.up ℤ)) (𝟙 _) I
  simp only [NatTrans.id_app, Category.id_comp, roosDerivedUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Category.assoc] at h
  change DerivedCategory.Q.{w}.map (roosι I) ≫ κ.hom.app I ≫
    e.hom.app (DerivedCategory.Q.{w}.obj I) = η.app I at h
  rw [inclusion_eq, DerivedCategory.Q.{w}.map_comp, Category.assoc]
  change DerivedCategory.Q.{w}.map ((ordinaryLimitIso (A := A)).hom.app I) ≫
    (DerivedCategory.Q.{w}.map (roosι I) ≫ κ.hom.app I ≫
      e.hom.app (DerivedCategory.Q.{w}.obj I)) = _
  rw [h]
  change DerivedCategory.Q.map ((ordinaryLimitIso (A := A)).hom.app I) ≫
    (ordinaryUnit (A := A)).app I = _
  unfold ordinaryUnit
  change DerivedCategory.Q.map ((ordinaryLimitIso (A := A)).hom.app I) ≫
    (DerivedCategory.Q.map ((ordinaryLimitIso (A := A)).inv.app I) ≫
      (unitNat (limitFunctor (A))).app I) = _
  rw [unitNat_app, ← Category.assoc, ← DerivedCategory.Q.map_comp,
    Iso.hom_inv_id_app, DerivedCategory.Q.map_id, Category.id_comp]

private theorem roosComparison_exists {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    (comm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u} R)] :
    ∃ theta : (roosF (A := ringedSiteModules.{u} R)) ⋙
      (DerivedCategory.Q : CochainComplex (ringedSiteModules.{u} R) ℤ ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} R)) ≅
      (DerivedCategory.Q : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ℤ ⥤
        DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)) ⋙
      (limitFunctor (ringedSiteModules.{u} R)).rightDerivedFunctor,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ℤ,
        DerivedCategory.Q.{w}.map (limitInclusion I) ≫ theta.hom.app I =
        unit (limitFunctor (ringedSiteModules.{u} R)) I := by
  obtain ⟨CF, κ, hCF, _⟩ := strictRoosDerivation.{u, u, u, w} J R comm
  have := hCF
  exact roosComparison_of_derived CF κ

private theorem augmentation_restriction_coherence
    {A : Type a} {B : Type b} {E : Type e}
    [Category.{v} A] [Category.{z} B] [Category.{ev} E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)]
    [Abelian.HasKInjectiveResolutions E]
    (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : A ⥤ E) (H' : B ⥤ E) [H.Additive] [H'.Additive]
    (rho : H.rightDerivedFunctor ⟶ F.mapDerivedCategory ⋙ H'.rightDerivedFunctor)
    (rhoT : (tower H).rightDerivedFunctor ⟶
      (tower F).mapDerivedCategory ⋙ (tower H').rightDerivedFunctor)
    (lambda : (limitFunctor A).rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      (tower F).mapDerivedCategory ⋙ (limitFunctor B).rightDerivedFunctor)
    (aR : (limitFunctor A).rightDerivedFunctor ⋙ H.rightDerivedFunctor ≅
      (tower H).rightDerivedFunctor ⋙ (limitFunctor E).rightDerivedFunctor)
    (aS : (limitFunctor B).rightDerivedFunctor ⋙ H'.rightDerivedFunctor ≅
      (tower H').rightDerivedFunctor ⋙ (limitFunctor E).rightDerivedFunctor)
    (theta : roosF (A := A) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor A).rightDerivedFunctor)
    (thetaS : roosF (A := B) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor B).rightDerivedFunctor)
    (hl : InverseLimitUnit F lambda)
    (ht : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.map (limitInclusion I) ≫ theta.hom.app I =
      unit (limitFunctor A) I)
    (htS : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      DerivedCategory.Q.map (limitInclusion I) ≫ thetaS.hom.app I =
      unit (limitFunctor B) I)
    (hcoh :
      ∀ M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
      rho.app ((limitFunctor A).rightDerivedFunctor.obj M) ≫
        H'.rightDerivedFunctor.map (lambda.hom.app M) ≫
        aS.hom.app ((tower F).mapDerivedCategory.obj M) =
      aR.hom.app M ≫ (limitFunctor E).rightDerivedFunctor.map (rhoT.app M)) :
    ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (P : CochainComplex A ℤ)
        (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
        (hgamma : ∀ n : ℕ, gamma (n + 1) ≫
          X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        rho.app (DerivedCategory.Q.obj P) ≫
            H'.rightDerivedFunctor.map
              (F.mapDerivedCategoryFactors.hom.app P ≫
                DerivedCategory.Q.map
                  (roosAugment
                    (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
                    (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n))
                    (fun n ↦ by
                      change (F.mapHomologicalComplex (.up ℤ)).map (gamma (n + 1)) ≫
                        (F.mapHomologicalComplex (.up ℤ)).map
                          (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
                      rw [← Functor.map_comp, hgamma n])) ≫
                thetaS.hom.app (((tower F).mapHomologicalComplex (.up ℤ)).obj X) ≫
                (limitFunctor B).rightDerivedFunctor.map
                  ((tower F).mapDerivedCategoryFactors.inv.app X)) ≫
            aS.hom.app ((tower F).mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
          H.rightDerivedFunctor.map
              (DerivedCategory.Q.map (roosAugment gamma hgamma) ≫ theta.hom.app X) ≫
            aR.hom.app (DerivedCategory.Q.obj X) ≫
            (limitFunctor E).rightDerivedFunctor.map
              (rhoT.app (DerivedCategory.Q.obj X)) := by
  intro X P gamma hgamma
  have haug := augmentation_unit_comparison F lambda hl gamma hgamma
  have haugA : DerivedCategory.Q.map (roosAugment gamma hgamma) ≫ theta.hom.app X =
      DerivedCategory.Q.map (augmentationLimit gamma hgamma) ≫
        unit (limitFunctor A) X := by
    rw [augmentationLimit_factor, DerivedCategory.Q.map_comp, Category.assoc, ht]
  have haugB := fun hgamma' ↦ augmentationLimit_factor
    (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
    (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n)) hgamma'
  have haugS : ∀ hgamma',
      DerivedCategory.Q.map (roosAugment
        (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
        (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n)) hgamma') ≫
        thetaS.hom.app (((tower F).mapHomologicalComplex (.up ℤ)).obj X) =
      DerivedCategory.Q.map (augmentationLimit
        (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
        (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n)) hgamma') ≫
        unit (limitFunctor B)
          (((tower F).mapHomologicalComplex (.up ℤ)).obj X) := by
    intro hgamma'
    rw [haugB, DerivedCategory.Q.map_comp, Category.assoc, htS]
  rw [haugA]
  rw [reassoc_of% haugS _]
  rw [← haug, H'.rightDerivedFunctor.map_comp]
  try simp only [Category.assoc]
  erw [← rho.naturality_assoc]
  try simp only [Functor.comp_map, Category.assoc]
  rw [hcoh]

/-- Fixed comparisons, with their common normalization and coherence proofs. -/
private structure ComparisonData
    {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{v} A] [IsGrothendieckAbelian.{z} B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ AddCommGrpCat.{u}]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Abelian.HasKInjectiveResolutions AddCommGrpCat.{u}]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (H : A ⥤ AddCommGrpCat.{u}) (H' : B ⥤ AddCommGrpCat.{u}) [H.Additive] [H'.Additive]
    [PreservesLimitsOfShape ℕᵒᵖ H] [PreservesLimitsOfShape ℕᵒᵖ H']
    (c : G ⋙ H ≅ H')
    (theta : roosF (A := A) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor A).rightDerivedFunctor)
    (thetaS : roosF (A := B) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor B).rightDerivedFunctor)
    : Type _ where
  rho : H.rightDerivedFunctor ⟶
        F.mapDerivedCategory ⋙ H'.rightDerivedFunctor
  rhoT : (tower H).rightDerivedFunctor ⟶
        (tower F).mapDerivedCategory ⋙ (tower H').rightDerivedFunctor
  lambda : (limitFunctor A).rightDerivedFunctor ⋙
          F.mapDerivedCategory ≅ (tower F).mapDerivedCategory ⋙
            (limitFunctor B).rightDerivedFunctor
  aR : (limitFunctor A).rightDerivedFunctor ⋙
          H.rightDerivedFunctor ≅ (tower H).rightDerivedFunctor ⋙
            (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor
  aS : (limitFunctor B).rightDerivedFunctor ⋙
          H'.rightDerivedFunctor ≅ (tower H').rightDerivedFunctor ⋙
            (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor
  eR : ∀ n : ℕᵒᵖ, (tower H).rightDerivedFunctor ⋙ evaluate n ≅
        evaluate n ⋙ H.rightDerivedFunctor
  eS : ∀ n : ℕᵒᵖ, (tower H').rightDerivedFunctor ⋙ evaluate n ≅
        evaluate n ⋙ H'.rightDerivedFunctor
  coherence :
      IsRestriction F G adj H H' c rho ∧
      IsRestriction (tower F) (tower G)
        (adj.whiskerRight ℕᵒᵖ) (tower H) (tower H')
        (NatIso.ofComponents (fun T ↦
          NatIso.ofComponents (fun n ↦ c.app (T.obj n)) (fun t ↦ c.hom.naturality (T.map t)))
          (fun t ↦ by apply NatTrans.ext; funext n; exact c.hom.naturality (t.app n))) rhoT ∧
      IsInverseLimitComparison F lambda ∧
      IsLimitComparison H aR ∧ IsLimitComparison H' aS ∧
      IsEvaluationComparison H eR ∧ IsEvaluationComparison H' eS ∧
      (∀ (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A)) (n : ℕᵒᵖ),
        (evaluate n).map (rhoT.app M) ≫
            (eS n).hom.app ((tower F).mapDerivedCategory.obj M) ≫
            H'.rightDerivedFunctor.map
              ((towerDerivedEvaluationInterchange F n).hom.app M) =
          (eR n).hom.app M ≫ rho.app ((evaluate n).obj M)) ∧
      IsRoosComparison theta ∧ IsRoosComparison thetaS ∧
      (∀ M : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
        rho.app ((limitFunctor A).rightDerivedFunctor.obj M) ≫
            H'.rightDerivedFunctor.map (lambda.hom.app M) ≫
            aS.hom.app ((tower F).mapDerivedCategory.obj M) =
          aR.hom.app M ≫ (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor.map
            (rhoT.app M)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (P : CochainComplex A ℤ)
        (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
        (hgamma : ∀ n : ℕ, gamma (n + 1) ≫
          X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        rho.app (DerivedCategory.Q.obj P) ≫
            H'.rightDerivedFunctor.map
              (F.mapDerivedCategoryFactors.hom.app P ≫
                DerivedCategory.Q.map
                  (roosAugment
                    (X := ((tower F).mapHomologicalComplex (.up ℤ)).obj X)
                    (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n))
                    (fun n ↦ by
                      change (F.mapHomologicalComplex (.up ℤ)).map (gamma (n + 1)) ≫
                        (F.mapHomologicalComplex (.up ℤ)).map
                          (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
                      rw [← Functor.map_comp, hgamma n])) ≫
                thetaS.hom.app (((tower F).mapHomologicalComplex (.up ℤ)).obj X) ≫
                (limitFunctor B).rightDerivedFunctor.map
                  ((tower F).mapDerivedCategoryFactors.inv.app X)) ≫
            aS.hom.app ((tower F).mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
          H.rightDerivedFunctor.map
              (DerivedCategory.Q.map (roosAugment gamma hgamma) ≫ theta.hom.app X) ≫
            aR.hom.app (DerivedCategory.Q.obj X) ≫
            (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor.map
              (rhoT.app (DerivedCategory.Q.obj X)))

@[irreducible] private def genericComparisons
    {A : Type a} {B : Type b}
    [Category.{v} A] [Category.{z} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{v} A] [IsGrothendieckAbelian.{z} B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ AddCommGrpCat.{u}]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Abelian.HasKInjectiveResolutions AddCommGrpCat.{u}]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (H : A ⥤ AddCommGrpCat.{u}) (H' : B ⥤ AddCommGrpCat.{u}) [H.Additive] [H'.Additive]
    [PreservesLimitsOfShape ℕᵒᵖ H] [PreservesLimitsOfShape ℕᵒᵖ H']
    (c : G ⋙ H ≅ H')
    (theta : roosF (A := A) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor A).rightDerivedFunctor)
    (thetaS : roosF (A := B) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ (limitFunctor B).rightDerivedFunctor)
    (ht : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.map (limitInclusion I) ≫ theta.hom.app I =
      unit (limitFunctor A) I)
    (htS : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      DerivedCategory.Q.map (limitInclusion I) ≫ thetaS.hom.app I =
      unit (limitFunctor B) I) : ComparisonData F G adj H H' c theta thetaS := by
  let rho := (restriction_exists F G adj
    H H' c).choose
  have hr := (restriction_exists F G adj
    H H' c).choose_spec
  let rhoT := (restriction_exists (tower F) (tower G)
    (adj.whiskerRight ℕᵒᵖ) (tower H) (tower H') (towerIso c)).choose
  have hrt := (restriction_exists (tower F) (tower G)
    (adj.whiskerRight ℕᵒᵖ) (tower H) (tower H')
    (towerIso c)).choose_spec
  let lambda := (inverseLimitComparison_exists F).choose
  have hl := (inverseLimitComparison_exists F).choose_spec
  let aR := (limitComparison_exists H).choose
  have haR := (limitComparison_exists H).choose_spec
  let aS := (limitComparison_exists H').choose
  have haS := (limitComparison_exists H').choose_spec
  let eR := (evaluationComparison_exists H).choose
  have heR := (evaluationComparison_exists H).choose_spec
  let eS := (evaluationComparison_exists H').choose
  have heS := (evaluationComparison_exists H').choose_spec
  refine ⟨rho, rhoT, lambda, aR, aS, eR, eS,
    ⟨(fun I T v _ _ _ ↦ hr I T v), (fun I T v _ _ _ ↦ hrt I T v),
    (fun I T v _ _ _ ↦ hl I T v), haR, haS, heR, heS, ?_,
    (fun I _ _ ↦ ht I), (fun I _ _ ↦ htS I), ?_, ?_⟩⟩
  · exact evaluation_restriction_coherence F G adj
      H H' c rho rhoT eR eS hr hrt heR heS
  · exact limit_restriction_coherence F G adj
      H H' c rho rhoT lambda aR aS hr hrt hl haR haS
  · exact augmentation_restriction_coherence F H H'
      rho rhoT lambda aR aS theta thetaS hl ht htS
      (limit_restriction_coherence F G adj
        H H' c rho rhoT lambda aR aS hr hrt hl haR haS)

attribute [local irreducible] roosF

section Statement
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasTerminal C] [HasTerminal D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
  [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
  [HasDerivedCategory.{w} AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ AddCommGrpCat.{u})]

/-- Actual sections restriction commutes with normalized strict derived inverse limit.

Source: blueprint det-sf-comp-coherence-refinement (2), integral comparison; Stacks
0940, 0941, 0A07, 0D6E, 08BJ, 070I and 09T5
(blueprint: lem-sfb-ringed-restriction-strict-limit-coherence).

The coefficient isomorphism in x identifies S with h⁻¹R and its structural map with
identity. All derived categories are ordinary and unbounded. IsSectionsComparison fixes
c from the geometric adjunction. IsRestriction fixes rho and rhoT by applying actual
sections to G(v) eta on K-injectives; this is precisely the derived-adjunction unit
followed by the sections/direct-image comparison. The tower version uses the whiskered
ordinary adjunction and comparison, so contains every transition, not just evaluations.
IsInverseLimitComparison fixes lambda by the resolution description of the normalized
exact-product comparison. IsLimitComparison fixes both a's by the common direct-image
unit equation. No restriction map is required to be invertible.

Proof:
1. Identify sections with maps from the singleton sheaf. The geometric adjunction and
   its terminal-object comparison give the additive ordinary sections isomorphism.
2. Derive the underived restriction transformation by the universal property of the
   right derived functor. Its normalization holds on all complexes and all chain maps.
3. Package derived evaluation into a tower-valued functor. The normalized evaluation
   comparison then gives both the levelwise comparisons and their transition equations.
4. Resolve K-injective towers by towers with injective terms. Their transitions split;
   applying any additive functor preserves the splittings. The split Roos sequence and
   exact products prove inverse-limit acyclicity, in the chosen derived-category universe.
5. Apply the universal derived composite comparisons to sections and exact inverse image.
   They give the specified limit comparisons, normalized on arbitrary complexes.
6. Check the restriction/limit equation projectionwise before deriving. Naturality and
   cancellation of the units on K-injectives prove both derived coherence equations;
   localization extends them to all derived objects.
7. The strict Roos derivation and uniqueness of right derived functors give theta with
   its inclusion normalization on every complex, without choosing additional resolutions.
8. Factor any strict augmentation through the ordinary inverse limit. Naturality of
   restriction, the normalized inverse-image comparison, and the coherence equation
   establish the augmentation identity with these same choices of comparisons. -/
theorem ringedRestrictionStrictLimitCoherence
    (_commR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_commS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (x : UnboundedExactTower.ExactMorphism S R)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u} S)]
    [PreservesLimitsOfShape (Discrete ℕ) x.inverse] :
    ∃ (c : x.ringed.modules ⋙ sections R ≅ sections S)
      (rho : (sections R).rightDerivedFunctor ⟶
        x.inverse.mapDerivedCategory ⋙ (sections S).rightDerivedFunctor)
      (rhoT : (tower (sections R)).rightDerivedFunctor ⟶
        (tower x.inverse).mapDerivedCategory ⋙ (tower (sections S)).rightDerivedFunctor)
      (lambda : (limitFunctor (ringedSiteModules.{u} R)).rightDerivedFunctor ⋙
          x.inverse.mapDerivedCategory ≅ (tower x.inverse).mapDerivedCategory ⋙
            (limitFunctor (ringedSiteModules.{u} S)).rightDerivedFunctor)
      (aR : (limitFunctor (ringedSiteModules.{u} R)).rightDerivedFunctor ⋙
          (sections R).rightDerivedFunctor ≅ (tower (sections R)).rightDerivedFunctor ⋙
            (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor)
      (aS : (limitFunctor (ringedSiteModules.{u} S)).rightDerivedFunctor ⋙
          (sections S).rightDerivedFunctor ≅ (tower (sections S)).rightDerivedFunctor ⋙
            (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor)
      (eR : ∀ n : ℕᵒᵖ, (tower (sections R)).rightDerivedFunctor ⋙ evaluate n ≅
        evaluate n ⋙ (sections R).rightDerivedFunctor)
      (eS : ∀ n : ℕᵒᵖ, (tower (sections S)).rightDerivedFunctor ⋙ evaluate n ≅
        evaluate n ⋙ (sections S).rightDerivedFunctor)
      (theta : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙
        (limitFunctor (ringedSiteModules.{u} R)).rightDerivedFunctor)
      (thetaS : roosF ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙
        (limitFunctor (ringedSiteModules.{u} S)).rightDerivedFunctor),
      IsSectionsComparison x.ringed c ∧
      IsRestriction x.inverse x.ringed.modules x.adjunction (sections R) (sections S) c rho ∧
      IsRestriction (tower x.inverse) (tower x.ringed.modules)
        (x.adjunction.whiskerRight ℕᵒᵖ) (tower (sections R)) (tower (sections S))
        (NatIso.ofComponents (fun T ↦
          NatIso.ofComponents (fun n ↦ c.app (T.obj n)) (fun t ↦ c.hom.naturality (T.map t)))
          (fun t ↦ by apply NatTrans.ext; funext n; exact c.hom.naturality (t.app n))) rhoT ∧
      IsInverseLimitComparison x.inverse lambda ∧
      IsLimitComparison (sections R) aR ∧ IsLimitComparison (sections S) aS ∧
      IsEvaluationComparison (sections R) eR ∧ IsEvaluationComparison (sections S) eS ∧
      (∀ (M : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)) (n : ℕᵒᵖ),
        (evaluate n).map (rhoT.app M) ≫
            (eS n).hom.app ((tower x.inverse).mapDerivedCategory.obj M) ≫
            (sections S).rightDerivedFunctor.map
              ((towerDerivedEvaluationInterchange x.inverse n).hom.app M) =
          (eR n).hom.app M ≫ rho.app ((evaluate n).obj M)) ∧
      IsRoosComparison theta ∧ IsRoosComparison thetaS ∧
      (∀ M : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R),
        rho.app ((limitFunctor (ringedSiteModules.{u} R)).rightDerivedFunctor.obj M) ≫
            (sections S).rightDerivedFunctor.map (lambda.hom.app M) ≫
            aS.hom.app ((tower x.inverse).mapDerivedCategory.obj M) =
          aR.hom.app M ≫ (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor.map
            (rhoT.app M)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ℤ)
        (P : CochainComplex (ringedSiteModules.{u} R) ℤ)
        (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
        (hgamma : ∀ n : ℕ, gamma (n + 1) ≫
          X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        rho.app (DerivedCategory.Q.obj P) ≫
            (sections S).rightDerivedFunctor.map
              (x.inverse.mapDerivedCategoryFactors.hom.app P ≫
                DerivedCategory.Q.map
                  (roosAugment
                    (X := ((tower x.inverse).mapHomologicalComplex (.up ℤ)).obj X)
                    (fun n ↦ (x.inverse.mapHomologicalComplex (.up ℤ)).map (gamma n))
                    (fun n ↦ by
                      change (x.inverse.mapHomologicalComplex (.up ℤ)).map (gamma (n + 1)) ≫
                        (x.inverse.mapHomologicalComplex (.up ℤ)).map
                          (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
                      rw [← Functor.map_comp, hgamma n])) ≫
                thetaS.hom.app (((tower x.inverse).mapHomologicalComplex (.up ℤ)).obj X) ≫
                (limitFunctor (ringedSiteModules.{u} S)).rightDerivedFunctor.map
                  ((tower x.inverse).mapDerivedCategoryFactors.inv.app X)) ≫
            aS.hom.app ((tower x.inverse).mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
          (sections R).rightDerivedFunctor.map
              (DerivedCategory.Q.map (roosAugment gamma hgamma) ≫ theta.hom.app X) ≫
            aR.hom.app (DerivedCategory.Q.obj X) ≫
            (limitFunctor AddCommGrpCat.{u}).rightDerivedFunctor.map
              (rhoT.app (DerivedCategory.Q.obj X))) := by
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses J R
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} S) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses K S
  have : PreservesLimitsOfShape ℕᵒᵖ x.inverse := natProducts_preservesTowers x.inverse
  let c := (sectionsComparison_exists x.ringed).choose
  have hc := (sectionsComparison_exists x.ringed).choose_spec
  obtain ⟨theta, ht⟩ := roosComparison_exists R _commR
  obtain ⟨thetaS, htS⟩ := roosComparison_exists S _commS
  let d := genericComparisons
    x.inverse x.ringed.modules x.adjunction (sections R) (sections S) c theta thetaS ht htS
  exact ⟨c, d.rho, d.rhoT, d.lambda, d.aR, d.aS, d.eR, d.eS,
    theta, thetaS, hc, d.coherence⟩


end Statement
end CategoryTheory.RingedRestrictionLimit
