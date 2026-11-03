/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Cochain.CochainHomotopyComparison
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Native coefficient reduction and total inverse limit

These are the section-ring presentations of the actual pulled-back condensed integer
ring. The ordinary right adjoint is inverse limit after scalar restriction. Its universal
right derived comparison and its representative normalization fix the completion unit.
Source: current blueprint, sk-lem-sp-tower, first paragraph; Stacks 0940 and 09T5.
The constructions specialize the coefficient part of IntegralDirectImageTowerData,
without its geometric operations or its import of the reconstruction theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Native integral derived modules, with no completeness condition. -/
abbrev Integral :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (spIntegralCondensed l E) T))

/-- Canonical derived completeness in the equal continuous-ring presentation.
The equality of the derived object, rather than existence of an unrelated complete
object, fixes which completion map is tested. -/
def Complete (K : Integral l E T) : Prop :=
  ∃ K' : DerivedCategory (AdicCompletion.Modules l E T),
    HEq K K' ∧ IsDerivedComplete l E T K'

/-- Exact section/internal presentation equivalence. -/
def sectionEquivalence : Integral l E T ≌ DerivedCategory (spIntegralSectionModules l E T) :=
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  (spIntegralModuleEquivalence l E T).mapDerivedCategory

variable (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)

attribute [local instance] SpReductionTower.additive

/-- Simultaneous derived reduction of native internal modules. -/
def red : Integral l E T ⥤ spDerivedCoefficientTowers l E T D :=
  (sectionEquivalence l E T).functor ⋙ R.red

/-- Restriction along the normalized section-ring comparison. -/
abbrev completedRestriction :=
  restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom)

/-- The strict tower after restricting every finite scalar action to R_T. Its
transitions are the actual quotient-semilinear transitions, retained before derivation.
Source: blueprint, clause (2) (blueprint: lem-sp-native-tower-limit-adjunction). -/
def restrictedTower :
    spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ spIntegralSectionModules l E T) :=
  (Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T D n ⋙
      completedRestriction l E T D R)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T D n)
      (completedRestriction l E T D R))).flip

/-- The actual ordinary inverse limit of that restricted strict tower.
Source: blueprint, clause (2) (blueprint: lem-sp-native-tower-limit-adjunction). -/
def ordinaryLimit :=
  restrictedTower l E T D R ⋙ Limits.lim

/-- The n-th ordinary inverse-limit projection, with its original finite-level sections.
Source: blueprint, clause (2) (blueprint: lem-sp-native-tower-limit-adjunction). -/
def ordinaryProjection
    (C : spCoefficientTowers l E T) (n : ℕ) :=
  limit.π ((restrictedTower l E T D R).obj C) (op n)

/-- Normalization of the ordinary tensor/limit adjunction on local tensor generators.
Source: blueprint, clause (2) (blueprint: lem-sp-native-tower-limit-adjunction). -/
def IsOrdinaryAdjunctionNormalized
    (adj : R.ordinary ⊣ ordinaryLimit l E T D R) : Prop :=
  ∀ (P : spIntegralSectionModules l E T) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : P.val.obj U),
    (ordinaryProjection l E T D R (R.ordinary.obj P) n).val.app U
        ((adj.unit.app P).val.app U x) =
      ((R.level n).inv.app P).val.app U
        (systemModelTmul (D.scalar
          (spIntegralReductionScalar l E T R.coefficient n)).model P U 1 x)

/-- Representative normalization of the derived tensor/limit adjunction.
Source: blueprint, clause (2) (blueprint: lem-sp-native-tower-limit-adjunction). -/
def IsDerivedAdjunctionNormalized
    [(ordinaryLimit l E T D R).Additive]
    (ordinaryAdjunction : R.ordinary ⊣ ordinaryLimit l E T D R)
    (derived : spDerivedCoefficientTowers l E T D ⥤
      DerivedCategory (spIntegralSectionModules l E T))
    (unit : (ordinaryLimit l E T D R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      spTowerLocalization l E T D ⋙ derived)
    (adjunction : R.red ⊣ derived) : Prop :=
  ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (I : CochainComplex (spCoefficientTowers l E T) ℤ)
    (v : (R.ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P)
        ((spTowerLocalization l E T D).obj I)
        (R.counit.app P ≫
          (spTowerLocalization l E T D).map v) =
      DerivedCategory.Q.map
        ((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I v) ≫ unit.app I

/-- Universal presentation of total derived inverse limit. Ordinary reduction tensors
with each quotient; its right adjoint is precisely the inverse limit of the restricted
finite modules. Both the ordinary and derived universal properties are retained.
The representative equation fixes the derived adjunction to the ordinary one.
Source: blueprint, clause (2), strict tower inverse limit; Stacks 0940 and 09T5
(blueprint: lem-sp-native-tower-limit-adjunction). -/
structure Limit where
  [additive : (ordinaryLimit l E T D R).Additive]
  ordinaryAdjunction : R.ordinary ⊣ ordinaryLimit l E T D R
  ordinary_normalization : IsOrdinaryAdjunctionNormalized l E T D R ordinaryAdjunction
  derived : spDerivedCoefficientTowers l E T D ⥤
    DerivedCategory (spIntegralSectionModules l E T)
  unit : (ordinaryLimit l E T D R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    spTowerLocalization l E T D ⋙ derived
  universal : derived.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso (spCoefficientTowers l E T) (.up ℤ))
  computes : ∀ I : CochainComplex (spCoefficientTowers l E T) ℤ,
    I.IsKInjective → IsIso (unit.app I)
  adjunction : R.red ⊣ derived
  normalization : IsDerivedAdjunctionNormalized l E T D R ordinaryAdjunction derived unit
    adjunction

/-- The total derived limit, with values back in internal integral modules.
Source: blueprint, clause (2) (blueprint: lem-sp-native-tower-limit-adjunction). -/
def lim (L : Limit l E T D R) :=
  L.derived ⋙ (sectionEquivalence l E T).inverse

/-- The canonical reduction/limit adjunction, transported through the exact equivalence.
Source: blueprint, canonical completion comparison in clause (2)
(blueprint: lem-sp-native-tower-limit-adjunction). -/
def redLimitAdjunction (L : Limit l E T D R) :
    red l E T D R ⊣ lim l E T D R L :=
  (sectionEquivalence l E T).toAdjunction.comp L.adjunction


private abbrev scalar (n : ℕ) :=
  D.scalar (spIntegralReductionScalar l E T R.coefficient n)

private abbrev restrictionIso (n : ℕ) :
    spCompletedEllRestriction l E T n ⋙ completedRestriction l E T D R ≅
      restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (spIntegralReductionScalar l E T R.coefficient n)) :=
  systemScalarRestrictionComposition.{u + 1, u, u + 1}
    R.coefficient.hom (spCompletedEllCommProjection l E T n)
    (spIntegralReductionScalar l E T R.coefficient n) rfl

private theorem restrictedTower_succ
    (C : spCoefficientTowers l E T) (n : ℕ) :
    ((restrictedTower l E T D R).obj C).map (homOfLE (Nat.le_succ n)).op =
      (completedRestriction l E T D R).map
        ((spCompletedTransition l E T D n).app C) := by
  change ((Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T D n ⋙
      completedRestriction l E T D R)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T D n)
      (completedRestriction l E T D R))).map (homOfLE (Nat.le_succ n)).op).app C = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem restrictedTower_map
    (C : spCoefficientTowers l E T) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (x : (((restrictedTower l E T D R).obj C).obj (op n)).val.obj U) :
    (((restrictedTower l E T D R).obj C).map (homOfLE h).op).val.app U x =
      ((D.equivalence.functor.obj C).transition h).val.app U x := by
  induction n, h using Nat.le_induction with
  | base =>
      simpa using ((D.equivalence.functor.obj C).identity m U x).symm
  | succ n h ih =>
      rw [← homOfLE_comp h (Nat.le_succ n), op_comp, Functor.map_comp]
      rw [restrictedTower_succ]
      change (((restrictedTower l E T D R).obj C).map (homOfLE h).op).val.app U
        (((spCompletedTransition l E T D n).app C).val.app U x) = _
      have ht := (spCompletedTransition_existsUnique l E T D n).exists.choose_spec C U x
      exact (congrArg
        (fun y ↦ (((restrictedTower l E T D R).obj C).map (homOfLE h).op).val.app U y)
        ht).trans ((ih _).trans
          ((D.equivalence.functor.obj C).compose h (Nat.le_succ n) U x).symm)

private def family
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : R.ordinary.obj P ⟶ C) (n : ℕ) :
    P ⟶ ((restrictedTower l E T D R).obj C).obj (op n) :=
  (scalar l E T D R n).ordinaryAdj.homEquiv _ _
    ((R.level n).inv.app P ≫
      (D.equivalence.functor.map f).app n) ≫
    (restrictionIso l E T D R n).inv.app _

private theorem family_apply
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : R.ordinary.obj P ⟶ C) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : P.val.obj U) :
    (family l E T D R f n).val.app U x =
      ((D.equivalence.functor.map f).app n).val.app U
        (spReductionGenerator l E T D R.coefficient
          R.ordinary R.level P n U 1 x) := by
  rw [family, Adjunction.homEquiv_unit]
  change ((D.equivalence.functor.map f).app n).val.app U
    (((R.level n).inv.app P).val.app U
      (((scalar l E T D R n).ordinaryAdj.unit.app P).val.app U x)) = _
  rw [(scalar l E T D R n).unit_normalized]
  rfl

private theorem family_compatible
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : R.ordinary.obj P ⟶ C) (n : ℕ) :
    family l E T D R f (n + 1) ≫
      ((restrictedTower l E T D R).obj C).map (homOfLE (Nat.le_succ n)).op =
      family l E T D R f n := by
  rw [restrictedTower_succ]
  ext U x
  change (((spCompletedTransition l E T D n).app C).val.app U)
    ((family l E T D R f (n + 1)).val.app U x) = _
  refine ((spCompletedTransition_existsUnique l E T D n).exists.choose_spec C U
    ((family l E T D R f (n + 1)).val.app U x)).trans ?_
  rw [family_apply, family_apply]
  have h := congrArg (fun a ↦ a.val.app U
    (spReductionGenerator l E T D R.coefficient
      R.ordinary R.level P (n + 1) U 1 x))
    ((D.equivalence.functor.map f).comm (Nat.le_succ n))
  change ((D.equivalence.functor.obj C).transition (Nat.le_succ n)).val.app U
      (((D.equivalence.functor.map f).app (n + 1)).val.app U
        (spReductionGenerator l E T D R.coefficient
          R.ordinary R.level P (n + 1) U 1 x)) =
    (((D.equivalence.functor.map f).app n).val.app U)
      (spStrictTransitionSection T (spCoefficientCommRings l E T)
        (D.equivalence.functor.obj (R.ordinary.obj P))
        (Nat.le_succ n) U
        (spReductionGenerator l E T D R.coefficient
          R.ordinary R.level P (n + 1) U 1 x)) at h
  rw [R.transition, map_one] at h
  exact h

private def familyCone
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : R.ordinary.obj P ⟶ C) : Cone ((restrictedTower l E T D R).obj C) where
  pt := P
  π := NatTrans.ofOpSequence (family l E T D R f) (by
    intro n
    simpa using (family_compatible l E T D R f n).symm)

private def transpose
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : R.ordinary.obj P ⟶ C) : P ⟶ (ordinaryLimit l E T D R).obj C :=
  limit.lift _ (familyCone l E T D R f)

private theorem transpose_projection
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (f : R.ordinary.obj P ⟶ C) (n : ℕ) :
    transpose l E T D R f ≫ ordinaryProjection l E T D R C n = family l E T D R f n :=
  limit.lift_π _ _

private def untransposeLevel
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E T D R).obj C) (n : ℕ) :
    (D.equivalence.functor.obj (R.ordinary.obj P)).level n ⟶
      (D.equivalence.functor.obj C).level n :=
  (R.level n).hom.app P ≫
    ((scalar l E T D R n).ordinaryAdj.homEquiv _ _).symm
      (h ≫ ordinaryProjection l E T D R C n ≫ (restrictionIso l E T D R n).hom.app _)

private theorem untransposeLevel_generator
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E T D R).obj C) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : P.val.obj U) :
    (untransposeLevel l E T D R h n).val.app U
      (spReductionGenerator l E T D R.coefficient
        R.ordinary R.level P n U 1 x) =
      (ordinaryProjection l E T D R C n).val.app U (h.val.app U x) := by
  have hi := congrArg (fun a ↦ a.val.app U
    (systemModelTmul (scalar l E T D R n).model P U 1 x))
    ((R.level n).inv_hom_id_app P)
  dsimp only [spReductionGenerator, untransposeLevel]
  change (((scalar l E T D R n).ordinaryAdj.homEquiv _ _).symm _).val.app U
    (((R.level n).hom.app P).val.app U
      (((R.level n).inv.app P).val.app U _)) = _
  change ((((R.level n).hom.app P).val.app U)
    (((R.level n).inv.app P).val.app U
      (systemModelTmul (scalar l E T D R n).model P U 1 x))) =
        systemModelTmul (scalar l E T D R n).model P U 1 x at hi
  rw [hi, systemScalarModel_transpose_tmul (scalar l E T D R n),
    Equiv.apply_symm_apply, one_smul]
  rfl

private def untransposeStrict
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E T D R).obj C) :
    D.equivalence.functor.obj (R.ordinary.obj P) ⟶
      D.equivalence.functor.obj C where
  app := untransposeLevel l E T D R h
  comm {m n} k := by
    apply (cancel_epi ((R.level n).inv.app P)).1
    apply systemScalarModel_hom_ext (scalar l E T D R n)
    intro U x
    change ((D.equivalence.functor.obj C).transition k).val.app U
      ((untransposeLevel l E T D R h n).val.app U
        (spReductionGenerator l E T D R.coefficient
          R.ordinary R.level P n U 1 x)) =
      (untransposeLevel l E T D R h m).val.app U
        (spStrictTransitionSection T (spCoefficientCommRings l E T)
          (D.equivalence.functor.obj (R.ordinary.obj P)) k U
          (spReductionGenerator l E T D R.coefficient
            R.ordinary R.level P n U 1 x))
    rw [R.transition, map_one,
      untransposeLevel_generator, untransposeLevel_generator]
    have hw := congrArg (fun a ↦ a.val.app U (h.val.app U x))
      (limit.w ((restrictedTower l E T D R).obj C) (homOfLE k).op)
    change (ordinaryProjection l E T D R C n ≫
      ((restrictedTower l E T D R).obj C).map (homOfLE k).op).val.app U
      (h.val.app U x) = _ at hw
    change (((restrictedTower l E T D R).obj C).map (homOfLE k).op).val.app U
      ((ordinaryProjection l E T D R C n).val.app U (h.val.app U x)) = _ at hw
    rw [restrictedTower_map] at hw
    exact hw

private def untranspose
    {P : spIntegralSectionModules l E T} {C : spCoefficientTowers l E T}
    (h : P ⟶ (ordinaryLimit l E T D R).obj C) : R.ordinary.obj P ⟶ C :=
  D.equivalence.functor.preimage (untransposeStrict l E T D R h)

private def ordinaryHomEquiv
    (P : spIntegralSectionModules l E T) (C : spCoefficientTowers l E T) :
    (R.ordinary.obj P ⟶ C) ≃ (P ⟶ (ordinaryLimit l E T D R).obj C) where
  toFun := transpose l E T D R
  invFun := untranspose l E T D R
  left_inv f := by
    apply D.equivalence.functor.map_injective
    rw [untranspose, Functor.map_preimage]
    apply strict_ext l E T
    intro n
    apply (cancel_epi ((R.level n).inv.app P)).1
    apply systemScalarModel_hom_ext (scalar l E T D R n)
    intro U x
    change (untransposeLevel l E T D R (transpose l E T D R f) n).val.app U
      (spReductionGenerator l E T D R.coefficient
        R.ordinary R.level P n U 1 x) = _
    rw [untransposeLevel_generator]
    have ht := congrArg (fun a ↦ a.val.app U x) (transpose_projection l E T D R f n)
    change (ordinaryProjection l E T D R C n).val.app U
      ((transpose l E T D R f).val.app U x) = _ at ht
    rw [family_apply] at ht
    exact ht
  right_inv h := by
    apply limit.hom_ext (F := (restrictedTower l E T D R).obj C)
    intro n
    change transpose l E T D R (untranspose l E T D R h) ≫
      ordinaryProjection l E T D R C n.unop = h ≫ ordinaryProjection l E T D R C n.unop
    rw [transpose_projection]
    ext U x
    rw [family_apply]
    dsimp only [untranspose]
    rw [Functor.map_preimage]
    change (untransposeLevel l E T D R h n.unop).val.app U
      (spReductionGenerator l E T D R.coefficient
        R.ordinary R.level P n.unop U 1 x) = _
    exact untransposeLevel_generator l E T D R h n.unop U x

private theorem reduction_map_generator
    {P Q : spIntegralSectionModules l E T} (f : P ⟶ Q) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : P.val.obj U) :
    (((D.equivalence.functor.map (R.ordinary.map f)).app n).val.app U)
      (spReductionGenerator l E T D R.coefficient
        R.ordinary R.level P n U 1 x) =
      spReductionGenerator l E T D R.coefficient
        R.ordinary R.level Q n U 1 (f.val.app U x) := by
  have hn := congrArg (fun a ↦ a.val.app U
    (systemModelTmul (scalar l E T D R n).model P U 1 x))
    ((R.level n).inv.naturality f)
  change ((R.level n).inv.app Q).val.app U
    (((scalar l E T D R n).model.E.map f).val.app U
      (systemModelTmul (scalar l E T D R n).model P U 1 x)) = _ at hn
  rw [systemScalarModel_map_tmul (scalar l E T D R n)] at hn
  exact hn.symm

private def ordinaryAdjunction :
    R.ordinary ⊣ ordinaryLimit l E T D R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := ordinaryHomEquiv l E T D R
    homEquiv_naturality_left_symm := by
      intro P Q C f h
      change untranspose l E T D R (f ≫ h) =
        R.ordinary.map f ≫ untranspose l E T D R h
      apply D.equivalence.functor.map_injective
      rw [untranspose, Functor.map_preimage, Functor.map_comp, untranspose,
        Functor.map_preimage]
      apply strict_ext l E T
      intro n
      apply (cancel_epi ((R.level n).inv.app P)).1
      apply systemScalarModel_hom_ext (scalar l E T D R n)
      intro U x
      change (untransposeLevel l E T D R (f ≫ h) n).val.app U
        (spReductionGenerator l E T D R.coefficient
          R.ordinary R.level P n U 1 x) =
        (untransposeLevel l E T D R h n).val.app U
          ((((D.equivalence.functor.map
            (R.ordinary.map f)).app n).val.app U)
            (spReductionGenerator l E T D R.coefficient
              R.ordinary R.level P n U 1 x))
      rw [reduction_map_generator, untransposeLevel_generator, untransposeLevel_generator]
      rfl
    homEquiv_naturality_right := by
      intro P C N f g
      apply limit.hom_ext (F := (restrictedTower l E T D R).obj N)
      intro n
      change transpose l E T D R (f ≫ g) ≫ ordinaryProjection l E T D R N n.unop =
        (transpose l E T D R f ≫ (ordinaryLimit l E T D R).map g) ≫
          ordinaryProjection l E T D R N n.unop
      have hn : (ordinaryLimit l E T D R).map g ≫
          ordinaryProjection l E T D R N n.unop =
          ordinaryProjection l E T D R C n.unop ≫
            (((restrictedTower l E T D R).map g).app n) :=
        limMap_π _ n
      rw [transpose_projection, Category.assoc, hn, ← Category.assoc,
        transpose_projection]
      ext U x
      change (family l E T D R (f ≫ g) n.unop).val.app U x =
        ((D.equivalence.functor.map g).app n.unop).val.app U
          ((family l E T D R f n.unop).val.app U x)
      rw [family_apply, family_apply, D.equivalence.functor.map_comp]
      rfl }

/-- Ordinary strict reduction is left adjoint to the inverse limit after restriction
of each quotient's scalar action, with unit given by one tensor the section.
Source: Stacks 03D7 and 0940; blueprint integral direct-image proof paragraph (2).
Proof: use the recorded level isomorphisms and normalized scalar adjunctions to
transpose every level of a strict tower map. The quotient-generator transition
formula makes these transposes a cone. The limit universal property gives a map
to the restricted limit. Conversely, transpose each limit projection and transport
back through the level isomorphisms. Tensor generation and compatibility of the
limit projections show that these maps form a strict tower morphism. The scalar
Hom equivalences and limit extensionality prove the two inverse identities and
naturality. At the identity tower map the transpose is the adjunction unit, and
its projections evaluate the scalar unit, giving exactly the stated normalization.
(blueprint: lem-sp-native-tower-limit-adjunction). -/
private theorem ordinary_limit_adjunction :
    ∃ adj : R.ordinary ⊣ ordinaryLimit l E T D R,
      IsOrdinaryAdjunctionNormalized l E T D R adj := by
  refine ⟨ordinaryAdjunction l E T D R, ?_⟩
  intro P n U x
  change (ordinaryProjection l E T D R (R.ordinary.obj P) n).val.app U
    ((transpose l E T D R (𝟙 (R.ordinary.obj P))).val.app U x) = _
  have ht := congrArg (fun a ↦ a.val.app U x)
    (transpose_projection l E T D R (𝟙 (R.ordinary.obj P)) n)
  change (ordinaryProjection l E T D R (R.ordinary.obj P) n).val.app U
    ((transpose l E T D R (𝟙 (R.ordinary.obj P))).val.app U x) = _ at ht
  rw [family_apply] at ht
  rw [D.equivalence.functor.map_id] at ht
  change (ordinaryProjection l E T D R (R.ordinary.obj P) n).val.app U
    ((transpose l E T D R (𝟙 (R.ordinary.obj P))).val.app U x) =
      spReductionGenerator l E T D R.coefficient
        R.ordinary R.level P n U 1 x at ht
  exact ht


/-- Derive a normalized ordinary reduction/limit adjunction using K-flat and K-injective
resolutions. Source: Stacks 09T5, 06YS and 07A6.
Proof: K-flat resolutions form a left resolving class. The fixed reduction counit is
invertible on this class, so its naturality proves that ordinary reduction inverts
quasi-isomorphisms between its objects. K-injective resolutions of the Grothendieck
category of strict towers construct the right derived limit. The resolving-class
adjunction theorem then gives the derived adjunction and its formula on every chain
map, with precisely the fixed counit. Ordinary normalization is retained unchanged.
(blueprint: lem-sp-native-tower-limit-adjunction). -/
private theorem derive
    (adj : R.ordinary ⊣ ordinaryLimit l E T D R)
    (hnorm : IsOrdinaryAdjunctionNormalized l E T D R adj) :
    Nonempty (Limit l E T D R) := by
  letI := D.hasDerived
  letI := D.grothendieck
  letI : Abelian.HasKInjectiveResolutions (spCoefficientTowers l E T) := inferInstance
  letI : (ordinaryLimit l E T D R).Additive := adj.right_adjoint_additive
  let G := R.ordinary
  let q := HomotopyCategory.quotient (spIntegralSectionModules l E T) (.up ℤ)
  let P : Set (HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ)) :=
    fun X ↦ ∃ K : CochainComplex (spIntegralSectionModules l E T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) K ∧
        q.obj K = X
  have hres : ∀ X : HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ),
      ∃ (X' : HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ)) (f : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso (spIntegralSectionModules l E T) (.up ℤ) f := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := spIntegralSectionRing l E T) K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  obtain ⟨εh, hεh, hεapp⟩ := exists_homotopy_leftDerived_comparison G
    R.red R.counit R.universal
  have hinv : ∀ X Y (f : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso (spIntegralSectionModules l E T) (.up ℤ) f →
      IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map f) := by
    rintro X Y f ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hf
    obtain ⟨f, rfl⟩ := q.map_surjective f
    have : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hf
    have : IsIso (εh.app (q.obj K)) := by
      rw [hεapp]
      exact R.computes K hK
    have : IsIso (εh.app (q.obj L)) := by
      rw [hεapp]
      exact R.computes L hL
    have : IsIso ((DerivedCategory.Qh ⋙ R.red).map (q.map f)) := by
      change IsIso (R.red.map (DerivedCategory.Q.map f))
      infer_instance
    exact IsIso.of_isIso_fac_left (εh.naturality (q.map f)).symm
  obtain ⟨RF, η, hR, hη⟩ := CategoryTheory.exists_derived (ordinaryLimit l E T D R)
  obtain ⟨d, hd⟩ := derivedAdjunctionOfResolvingClass G (ordinaryLimit l E T D R) adj
    P hres hinv R.red εh hεh RF η hR
  refine ⟨{
    ordinaryAdjunction := adj
    ordinary_normalization := hnorm
    derived := RF
    unit := η
    universal := hR
    computes := hη
    adjunction := d
    normalization := ?_ }⟩
  intro K I f
  rw [← hεapp K]
  exact hd K I f

/-- Simultaneous native reduction is left adjoint to the total derived inverse limit
of the scalar-restricted strict tower. The ordinary unit is the quotient map and the
representative equation fixes the derived completion unit, without any boundedness,
constructibility, Noetherian or residue-characteristic hypothesis.
Source: current blueprint sk-lem-sp-tower, first paragraph; Stacks 0940 and 09T5
(blueprint: lem-sp-native-tower-limit-adjunction).

Proof: transpose a tower morphism by the normalized scalar Hom equivalence at every
level. The strict quotient-generator formula makes these maps a compatible cone.
Conversely transpose the actual limit projections. Tensor generation and limit
extensionality prove the inverse and naturality equations. K-flat source resolutions
and K-injective tower resolutions derive this ordinary adjunction. The fixed left
comparison R.counit and the universal right comparison retain the chain-map transpose
formula, hence the actual unit and counit, on all localized morphisms. -/
theorem exists_limit : Nonempty (Limit l E T D R) := by
  obtain ⟨a, ha⟩ := ordinary_limit_adjunction l E T D R
  exact derive l E T D R a ha

end AlgebraicGeometry.ProEtale.NativeTower
