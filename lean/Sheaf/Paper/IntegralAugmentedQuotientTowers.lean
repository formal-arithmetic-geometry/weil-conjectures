/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.PulledReductionComparisonData
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomologicalComplex
import all Sheaf.Paper.ProEtaleConstantReductionModels
import all Sheaf.Paper.CompletedTowerPullback
import all Sheaf.Paper.StratumCompletionUnitRestriction
import all Sheaf.Paper.CompletedPullbackReduction
import all Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.IntegralConstantQuotientCokernel
import Sheaf.Paper.IntegralCompletedInsertionUnit
import all Sheaf.Paper.AdicCoefficientDatum

/-! # Generator-normalized augmented ordinary quotient towers

Source: main-20261015, det-lem-int-tensor-pullback.proof.md, first paragraph and
Comparison with the Stacks Project; Stacks 093J, 093M and 07A4.
(blueprint: lem-sfb-integral-augmented-quotient-towers).

All functors are the published ordinary module functors. A natural isomorphism between
these functors induces a chain isomorphism on every unbounded cochain complex by
NatIso.mapHomologicalComplex. A functor into the strict tower category retains all
transition maps. The natural-number index n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralAugmentedQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual uniformizer-adic datum, with the existing harmless coefficient size lift.
Source: first paragraph, det-lem-int-tensor-pullback.proof.md
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev datum := pbcIntegralDatum l E

/-- Completed-coefficient modules on the original small pro-etale site.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev modules (W : Scheme.{u}) := reductionModules W ((datum l E).completedRing W)

/-- The existing constant-function scalar restriction; this keeps the additive sheaf.
Source: det-lem-int-tensor-pullback.proof.md, comparison paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev res (W : Scheme.{u}) := PulledReduction.res (datum l E) W

/-- The published completed ordinary tensor quotient tower, with its actual transitions.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev redR (W : Scheme.{u}) := completedReductionModuleTowerFunctor W (datum l E)

/-- The published constant ordinary tensor quotient tower, with its actual transitions.
Source: det-lem-int-tensor-pullback.proof.md, comparison paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev redC (W : Scheme.{u}) := OrderedExchange.reductionModule (datum l E) W

/-- The existing natural balancing beta, before applying it degree by degree to complexes.
Its direction is constant tensor to restricted completed tensor.
Source: det-lem-int-tensor-pullback.proof.md, comparison paragraph; Stacks 093M
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev beta (W : Scheme.{u}) := OrderedExchange.ordinaryRho (datum l E) W

/-- The two reductions have the SAME cokernel of the prescribed uniformizer action.
The cokernel is a sheaf cokernel; no surjectivity on sections over every object is assumed.
The augmentation equations normalize both identifications, including the inverse of beta.
Source: det-lem-int-tensor-pullback.proof.md, comparison paragraph; Stacks 093J and 093M
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
def CommonQuotient (W : Scheme.{u}) (M : modules l E W) (n : ℕ) : Prop :=
  ∃ μ : End ((res l E W).obj M),
    (∀ (Z : W.ProEtᵒᵖ) (x : M.val.obj Z),
      μ.val.app Z x =
        @SMul.smul ((exchangeConstantRing W (PbcIntegralRing l E)).obj.obj Z)
          (((res l E W).obj M).val.obj Z) inferInstance
        ((toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))).app Z
            ((pbcUniformizer l E) ^ (n + 1))) x) ∧
    ∃ (c : cokernel μ ≅ ((redC l E W).obj ((res l E W).obj M)).obj (op n))
      (r : cokernel μ ≅ ((redR l E W).obj M ⋙ res l E W).obj (op n)),
      cokernel.π μ ≫ c.hom =
        ((OrderedExchange.ordinaryAugmentation (datum l E) W).app
          ((res l E W).obj M)).app (op n) ∧
      cokernel.π μ ≫ r.hom =
        (res l E W).map (((completedReductionModuleUnit (datum l E) W).app M).app
          (op n)) ∧
      c.hom ≫ ((beta l E W).hom.app M).app (op n) = r.hom

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The canonical completed-coefficient ordinary module inverse image.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev pullR := completedModulePullback g (datum l E)

/-- The canonical constant-coefficient ordinary module inverse image.
Source: det-lem-int-tensor-pullback.proof.md, comparison paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev pullC := PulledReduction.pull (A := PbcIntegralRing l E) g

/-- Termwise completed-coefficient pullback of the actual strict tower.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev towerPullR := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pullR l E g)

/-- Termwise constant-coefficient pullback of the actual strict tower.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev towerPullC := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pullC l E g)

/-- The source's tower T, before degreewise application to a complex.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev T := redR l E Y ⋙ towerPullR l E g

/-- The source's tower U, before degreewise application to a complex.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev U := pullR l E g ⋙ redR l E X

/-- The source's tower V, before degreewise application to a complex.
Source: det-lem-int-tensor-pullback.proof.md, comparison paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
abbrev V := res l E Y ⋙ redC l E Y ⋙ towerPullC l E g

attribute [local irreducible] pbcIntegralDatum
  HasDerivedCategory.standard Functor.mapDerivedCategory

/-- Theta is the specified composite d followed by pulled inverse beta, at all levels.
This is a definition of the actual comparison from the node, rather than an arbitrary map.
Source: det-lem-int-tensor-pullback.proof.md, comparison paragraph
(blueprint: lem-sfb-integral-augmented-quotient-towers). -/
def theta (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g) :
    T l E g ⋙ PulledReduction.tres (datum l E) X ≅ V l E g :=
  let build (A B C D : Type _) [Category A] [Category B] [Category C] [Category D]
      (F : A ⥤ B) (R : B ⥤ C) (S : A ⥤ D) (G : D ⥤ C)
      (H : A ⥤ ℕᵒᵖ ⥤ A) (K : D ⥤ ℕᵒᵖ ⥤ D)
      (δ : F ⋙ R ≅ S ⋙ G)
      (b : S ⋙ K ≅ H ⋙ (Functor.whiskeringRight ℕᵒᵖ A D).obj S) :
      (H ⋙ (Functor.whiskeringRight ℕᵒᵖ A B).obj F) ⋙
          (Functor.whiskeringRight ℕᵒᵖ B C).obj R ≅
        S ⋙ K ⋙ (Functor.whiskeringRight ℕᵒᵖ D C).obj G :=
    Functor.isoWhiskerLeft H (Functor.whiskeringRightObjCompIso F R) ≪≫
      Functor.isoWhiskerLeft H ((Functor.whiskeringRight ℕᵒᵖ A C).mapIso δ) ≪≫
      Functor.isoWhiskerRight b.symm ((Functor.whiskeringRight ℕᵒᵖ D C).obj G)
  build _ _ _ _ (pullR l E g) (res l E X) (res l E Y) (pullC l E g)
    (redR l E Y) (redC l E Y) d (beta l E Y)

private def sourceComparison :
    pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g :=
  Functor.isoWhiskerRight
    (eqToIso (completedModulePullback_eq_exact g (datum l E))) (res l E X) ≪≫
      exchangeOrdinaryResPull (datum l E) g

private theorem completedTowerComparison :
    ∃ a : T l E g ≅ U l E g,
      ∀ (M : modules l E Y) (n : ℕ),
        (pullR l E g).map
            (((completedReductionModuleUnit (datum l E) Y).app M).app (op n)) ≫
            (a.hom.app M).app (op n) =
          ((completedReductionModuleUnit (datum l E) X).app ((pullR l E g).obj M)).app
            (op n) := by
  unfold T U towerPullR pullR
  rw [completedModulePullback_eq_exact]
  refine ⟨stratumModuleReductionIso (datum l E) g, ?_⟩
  intro M n
  have hs := (stratumModuleReductionIso_exists (datum l E) g).exists.choose_spec M
  have hs' := congrArg (fun f ↦ f.app (op n)) hs
  dsimp only [NatTrans.comp_app, AdicCoefficientDatum.constantPullbackIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom, AdicCoefficientDatum.towerModulePull,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app] at hs'
  erw [Category.id_comp] at hs'
  exact hs'

private theorem insertion_unit (M : modules l E Y) (Z : Y.ProEtᵒᵖ)
    (x : M.val.obj Z) :
    ((eqToIso (completedModulePullback_eq_exact g (datum l E))).hom.app M).val.app
        ((proEtaleBaseChange g).op.obj Z)
        (PulledReduction.insertion (datum l E) g M Z x) =
      ((proEtaleRingModuleAdjunction g ((datum l E).completedRing Y)
        ((datum l E).completedRing X) ((datum l E).integralRingIso g)).unit.app M).val.app
          Z x := by
  exact completedInsertionUnit (datum l E) g
    (completedModulePullback_eq_exact g (datum l E)) M Z x

private theorem sourceComparison_normalized :
    PulledReduction.IsOrdinaryNormalized (datum l E) g (sourceComparison l E g).inv := by
  intro M Z x
  let e := eqToIso (completedModulePullback_eq_exact g (datum l E))
  let δ := exchangeOrdinaryResPull (datum l E) g
  have h := OrderedExchange.restrictionPullback_unit g
    (exchangeConstantRing Y (PbcIntegralRing l E)) ((datum l E).completedRing Y)
    (exchangeConstantRing X (PbcIntegralRing l E)) ((datum l E).completedRing X)
    (exchangeScalar (datum l E) Y) (exchangeScalar (datum l E) X)
    (exchangeConstantIso g (PbcIntegralRing l E)) ((datum l E).integralRingIso g)
    (exchangeScalar_comm (datum l E) g) M Z x
  have hi := insertion_unit l E g M Z x
  change (e.inv.app M).val.app ((proEtaleBaseChange g).op.obj Z)
    ((δ.inv.app M).val.app ((proEtaleBaseChange g).op.obj Z) _) = _
  change (δ.inv.app M).val.app ((proEtaleBaseChange g).op.obj Z) _ = _ at h
  rw [h, ← hi]
  have he := congrArg (fun f ↦ f.val.app ((proEtaleBaseChange g).op.obj Z)
    (PulledReduction.insertion (datum l E) g M Z x)) (e.hom_inv_id_app M)
  exact he

private theorem insertion_smul (M : modules l E Y) (Z : Y.ProEtᵒᵖ)
    (b : ((datum l E).completedRing Y).obj.obj Z) (x : M.val.obj Z) :
    PulledReduction.insertion (datum l E) g M Z (b • x) =
      ((proEtaleRingDirectImageMap g ((datum l E).completedRing Y)
        ((datum l E).completedRing X) ((datum l E).integralRingIso g)).hom.app Z b) •
          PulledReduction.insertion (datum l E) g M Z x := by
  let e := eqToIso (completedModulePullback_eq_exact g (datum l E))
  let adj := proEtaleRingModuleAdjunction g ((datum l E).completedRing Y)
    ((datum l E).completedRing X) ((datum l E).integralRingIso g)
  have h := ((adj.unit.app M).val.app Z).hom.map_smul b x
  change (adj.unit.app M).val.app Z (b • x) =
    ((proEtaleRingDirectImageMap g ((datum l E).completedRing Y)
      ((datum l E).completedRing X) ((datum l E).integralRingIso g)).hom.app Z b) •
        (show ((proEtaleRingModulePullback g ((datum l E).completedRing Y)
          ((datum l E).completedRing X) ((datum l E).integralRingIso g)).obj M).val.obj
            ((proEtaleBaseChange g).op.obj Z) from (adj.unit.app M).val.app Z x) at h
  rw [← insertion_unit l E g M Z (b • x), ← insertion_unit l E g M Z x] at h
  have hc (y) := congrArg (fun f ↦ f.val.app ((proEtaleBaseChange g).op.obj Z) y)
    (e.hom_inv_id_app M)
  have hh := congrArg (fun y ↦ (e.inv.app M).val.app
    ((proEtaleBaseChange g).op.obj Z) y) h
  rw [map_smul] at hh
  exact (hc _).symm.trans (hh.trans (congrArg (fun y ↦ _ • y) (hc _)))

private theorem insertion_naturality {M N : modules l E Y} (f : M ⟶ N)
    (Z : Y.ProEtᵒᵖ) (x : M.val.obj Z) :
    ((pullR l E g).map f).val.app ((proEtaleBaseChange g).op.obj Z)
        (PulledReduction.insertion (datum l E) g M Z x) =
      PulledReduction.insertion (datum l E) g N Z (f.val.app Z x) := by
  let e := eqToIso (completedModulePullback_eq_exact g (datum l E))
  let adj := proEtaleRingModuleAdjunction g ((datum l E).completedRing Y)
    ((datum l E).completedRing X) ((datum l E).integralRingIso g)
  have hu := congrArg (fun h ↦ h.val.app Z x) (adj.unit.naturality f)
  change (adj.unit.app N).val.app Z (f.val.app Z x) =
    ((proEtaleRingModulePullback g ((datum l E).completedRing Y)
      ((datum l E).completedRing X) ((datum l E).integralRingIso g)).map f).val.app
        ((proEtaleBaseChange g).op.obj Z) ((adj.unit.app M).val.app Z x) at hu
  have he := congrArg (fun h ↦ h.val.app ((proEtaleBaseChange g).op.obj Z)
    (PulledReduction.insertion (datum l E) g M Z x)) (e.hom.naturality f)
  rw [← insertion_unit l E g N Z (f.val.app Z x),
    ← insertion_unit l E g M Z x] at hu
  have hh := congrArg (fun y ↦ (e.inv.app N).val.app
    ((proEtaleBaseChange g).op.obj Z) y) (he.trans hu.symm)
  have hc (y) := congrArg (fun h ↦ h.val.app ((proEtaleBaseChange g).op.obj Z) y)
    (e.hom_inv_id_app N)
  exact (hc _).symm.trans (hh.trans (hc _))

private theorem completed_tensor
    (a : T l E g ≅ U l E g)
    (ha : ∀ (M : modules l E Y) (n : ℕ),
      (pullR l E g).map
        (((completedReductionModuleUnit (datum l E) Y).app M).app (op n)) ≫
        (a.hom.app M).app (op n) =
      ((completedReductionModuleUnit (datum l E) X).app ((pullR l E g).obj M)).app (op n))
    (M : modules l E Y) (n : ℕ) (Z : Y.ProEtᵒᵖ)
    (s : ((datum l E).finiteRing Y n).obj.obj Z) (x : M.val.obj Z) :
    ((a.hom.app M).app (op n)).val.app ((proEtaleBaseChange g).op.obj Z)
      (PulledReduction.insertion (datum l E) g
        ((completedReductionLevel Y (datum l E) n).obj M) Z
        (reductionTensorSection Y ((datum l E).projection Y n) M Z s x)) =
      reductionTensorSection X ((datum l E).projection X n) ((pullR l E g).obj M)
        ((proEtaleBaseChange g).op.obj Z)
        ((proEtaleRingDirectImageMap g ((datum l E).finiteRing Y n)
          ((datum l E).finiteRing X n) ((datum l E).finiteRingIso g n)).hom.app Z s)
        (PulledReduction.insertion (datum l E) g M Z x) := by
  let qY := ((datum l E).projection Y n)
  let qX := ((datum l E).projection X n)
  let ηY := ((completedReductionModuleUnit (datum l E) Y).app M).app (op n)
  let ηX := ((completedReductionModuleUnit (datum l E) X).app
    ((pullR l E g).obj M)).app (op n)
  obtain ⟨b, hb⟩ := projection_surjective (datum l E) Y n Z s
  have hY : reductionTensorSection Y qY M Z s x = ηY.val.app Z (b • x) := by
    have h := (ηY.val.app Z).hom.map_smul b x
    change ηY.val.app Z (b • x) =
      (qY.hom.app Z b) • (show ((reductionChange Y qY).obj M).val.obj Z from
        ηY.val.app Z x) at h
    have hu := (completedReductionModuleUnit_exists (datum l E) Y).exists.choose_spec
      M n Z x
    change ηY.val.app Z x = reductionTensorSection Y qY M Z 1 x at hu
    rw [hu] at h
    rw [tensorSection_smul, mul_one, hb] at h
    exact h.symm
  erw [hY, ← insertion_naturality l E g ηY Z (b • x)]
  have haug := congrArg (fun f ↦ f.val.app ((proEtaleBaseChange g).op.obj Z)
    (PulledReduction.insertion (datum l E) g M Z (b • x))) (ha M n)
  change ((a.hom.app M).app (op n)).val.app _
    (((pullR l E g).map ηY).val.app _ _) = ηX.val.app _ _ at haug
  erw [haug]
  rw [insertion_smul]
  rw [map_smul]
  have hscalar := restrictionDirectImageMap_square g ((datum l E).completedRing Y)
    ((datum l E).finiteRing Y n) ((datum l E).completedRing X)
    ((datum l E).finiteRing X n) qY qX ((datum l E).integralRingIso g)
    ((datum l E).finiteRingIso g n) ((datum l E).projection_comm g n)
  have hscalar' := congrArg (fun f ↦ f.hom.app Z b) hscalar
  change (proEtaleRingDirectImageMap g ((datum l E).finiteRing Y n)
    ((datum l E).finiteRing X n) ((datum l E).finiteRingIso g n)).hom.app Z
      (qY.hom.app Z b) = qX.hom.app ((proEtaleBaseChange g).op.obj Z)
        ((proEtaleRingDirectImageMap g ((datum l E).completedRing Y)
          ((datum l E).completedRing X) ((datum l E).integralRingIso g)).hom.app Z b)
      at hscalar'
  have huX := (completedReductionModuleUnit_exists (datum l E) X).exists.choose_spec
    ((pullR l E g).obj M) n ((proEtaleBaseChange g).op.obj Z)
      (PulledReduction.insertion (datum l E) g M Z x)
  change ηX.val.app ((proEtaleBaseChange g).op.obj Z)
    (PulledReduction.insertion (datum l E) g M Z x) = _ at huX
  erw [huX]
  change qX.hom.app ((proEtaleBaseChange g).op.obj Z) _ •
    reductionTensorSection X qX ((pullR l E g).obj M)
      ((proEtaleBaseChange g).op.obj Z) 1
        (PulledReduction.insertion (datum l E) g M Z x) = _
  erw [tensorSection_smul, mul_one, ← hscalar', hb]

private theorem constantAugmentation_unit (W : Scheme.{u})
    (M : reductionModules W (exchangeConstantRing W (PbcIntegralRing l E))) (n : ℕ) :
    ((OrderedExchange.ordinaryAugmentation (datum l E) W).app M).app (op n) =
      (proEtaleRingExtensionAdjunction (OrderedExchange.quotient (datum l E) W n)).unit.app
        M := by
  ext Z x
  exact ((OrderedExchange.ordinaryAugmentation_existsUnique (datum l E) W).exists.choose_spec
    M n Z x).trans (OrderedExchange.levelUnitMap_apply (datum l E) W n M Z x).symm

private theorem constantTowerComparison :
    ∃ c : V l E g ≅ (res l E Y ⋙ pullC l E g) ⋙ redC l E X,
      ∀ (M : modules l E Y) (n : ℕ),
        (pullC l E g).map
            (((OrderedExchange.ordinaryAugmentation (datum l E) Y).app
              ((res l E Y).obj M)).app (op n)) ≫
            (c.hom.app M).app (op n) =
          ((OrderedExchange.ordinaryAugmentation (datum l E) X).app
            ((pullC l E g).obj ((res l E Y).obj M))).app (op n) := by
  refine ⟨Functor.isoWhiskerLeft (res l E Y)
    (OrderedExchange.ordinaryReductionPullIso (datum l E) g), ?_⟩
  intro M n
  change (pullC l E g).map _ ≫
    (OrderedExchange.levelPullIso (datum l E) g n).hom.app _ = _
  rw [constantAugmentation_unit, constantAugmentation_unit]
  exact OrderedExchange.levelPullIso_unit (datum l E) g n _

private theorem beta_augmentation (W : Scheme.{u}) (M : modules l E W) (n : ℕ) :
    (((OrderedExchange.ordinaryAugmentation (datum l E) W).app
      ((res l E W).obj M)).app (op n)) ≫ ((beta l E W).hom.app M).app (op n) =
      (res l E W).map (((completedReductionModuleUnit (datum l E) W).app M).app (op n)) := by
  ext Z x
  change (((beta l E W).hom.app M).app (op n)).val.app Z
    ((((OrderedExchange.ordinaryAugmentation (datum l E) W).app
      ((res l E W).obj M)).app (op n)).val.app Z x) =
    (((completedReductionModuleUnit (datum l E) W).app M).app (op n)).val.app Z x
  erw [(OrderedExchange.ordinaryAugmentation_existsUnique (datum l E) W).exists.choose_spec]
  exact ((OrderedExchange.ordinaryRho_existsUnique (datum l E) W).exists.choose_spec
    M n Z 1 x).trans
      ((completedReductionModuleUnit_exists (datum l E) W).exists.choose_spec M n Z x).symm

private theorem commonQuotient (W : Scheme.{u}) (M : modules l E W) (n : ℕ) :
    CommonQuotient l E W M n := by
  obtain ⟨μ, hμ, c, hc⟩ := constantQuotientCokernel l E W ((res l E W).obj M) n
  refine ⟨μ, hμ, c, c ≪≫ ((beta l E W).app M).app (op n), hc, ?_, ?_⟩
  · change cokernel.π μ ≫ (c.hom ≫ ((beta l E W).hom.app M).app (op n)) = _
    rw [← Category.assoc, hc]
    exact beta_augmentation l E W M n
  · rfl

private theorem inverse_unit {C : Type*} [Category C] {M N P : C}
    (f : M ⟶ N) (r : M ⟶ P) (e : N ≅ P) (h : f ≫ e.hom = r) :
    r ≫ e.inv = f := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem naturality_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (R : B ⥤ C) (S : A ⥤ D) (G : D ⥤ C)
    (d : F ⋙ R ≅ S ⋙ G) {M N : A} (f : M ⟶ N)
    {Z : D} (b : S.obj N ⟶ Z) (u : S.obj M ⟶ Z)
    (h : S.map f ≫ b = u) :
    R.map (F.map f) ≫ (d.hom.app N ≫ G.map b) = d.hom.app M ≫ G.map u := by
  rw [← Category.assoc]
  erw [d.hom.naturality f]
  change (d.hom.app M ≫ G.map (S.map f)) ≫ G.map b = _
  rw [Category.assoc, ← G.map_comp, h]

private theorem theta_augmentation
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (M : modules l E Y) (n : ℕ) :
    (res l E X).map ((pullR l E g).map
        (((completedReductionModuleUnit (datum l E) Y).app M).app (op n))) ≫
        ((theta l E g d).hom.app M).app (op n) =
      d.hom.app M ≫ (pullC l E g).map
        (((OrderedExchange.ordinaryAugmentation (datum l E) Y).app
          ((res l E Y).obj M)).app (op n)) := by
  have hbi := inverse_unit
    (((OrderedExchange.ordinaryAugmentation (datum l E) Y).app
      ((res l E Y).obj M)).app (op n))
    ((res l E Y).map (((completedReductionModuleUnit (datum l E) Y).app M).app (op n)))
    (((beta l E Y).app M).app (op n)) (beta_augmentation l E Y M n)
  change _ ≫ (d.hom.app _ ≫ (pullC l E g).map
    (((beta l E Y).inv.app M).app (op n))) = _
  exact naturality_unit (pullR l E g) (res l E X) (res l E Y) (pullC l E g) d
    (((completedReductionModuleUnit (datum l E) Y).app M).app (op n)) _ _ hbi

/-- Strict augmented quotient-tower comparisons for arbitrary, possibly unbounded complexes.
The isomorphisms are natural at the module level; applying mapHomologicalComplex yields
exactly the natural chain isomorphisms, with every differential and transition retained.
The last two identities are equalities in each strict tower, hence in every cochain degree.

Source: det-lem-int-tensor-pullback.proof.md, first and comparison paragraphs;
Stacks Tags 093J, 093M and 07A4
(blueprint: lem-sfb-integral-augmented-quotient-towers).

Proof:
1. Compare completed pullback with the canonical identified-coefficient pullback, and
compose with the published ordinary scalar-restriction comparison. The insertion-unit
transport lemma and the restriction-pullback unit formula give its normalization.
2. Use the published augmented completed-tower comparison. Every finite coefficient
section lifts to the completed ring. Linearity and naturality of insertion, the
augmentation equation and the coefficient square give the full tensor-generator formula.
3. Use the published ordinary constant-tower comparison and its adjunction-unit formula.
This is an isomorphism of strict towers, so transition maps are retained.
4. Apply constantQuotientCokernel to the restricted module. Compose its cokernel
identification with beta for the completed identification. The prescribed beta formula
at 1 tensor x proves the completed augmentation equation.
5. Naturality of the source comparison and the inverse beta augmentation equation prove
the theta augmentation equation. All constructions are natural module maps and strict
tower maps. Consequently they apply in every degree of arbitrary cochain complexes,
including torsion terms and finite tensors that are not K-flat.
-/
theorem augmentedQuotientTowers
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    (∀ (W : Scheme.{u}), W = X ∨ W = Y →
      ∀ (H : CochainComplex (modules l E W) ℤ) (j : ℤ) (n : ℕ),
        CommonQuotient l E W (H.X j) n) ∧
    ∃ (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
      (a : T l E g ≅ U l E g)
      (c : V l E g ≅ (res l E Y ⋙ pullC l E g) ⋙ redC l E X),
      PulledReduction.IsOrdinaryNormalized (datum l E) g d.inv ∧
      (  ∀ (M : modules l E Y) (n : ℕ) (Z : Y.ProEtᵒᵖ)
        (s : ((datum l E).finiteRing Y n).obj.obj Z) (x : M.val.obj Z),
        ((a.hom.app M).app (op n)).val.app ((proEtaleBaseChange g).op.obj Z)
          (PulledReduction.insertion (datum l E) g
            ((completedReductionLevel Y (datum l E) n).obj M) Z
            (reductionTensorSection Y ((datum l E).projection Y n) M Z s x)) =
          reductionTensorSection X ((datum l E).projection X n) ((pullR l E g).obj M)
            ((proEtaleBaseChange g).op.obj Z)
            ((proEtaleRingDirectImageMap g ((datum l E).finiteRing Y n)
              ((datum l E).finiteRing X n) ((datum l E).finiteRingIso g n)).hom.app Z s)
            (PulledReduction.insertion (datum l E) g M Z x)) ∧
      (∀ (M : modules l E Y) (n : ℕ),
        (pullR l E g).map
            (((completedReductionModuleUnit (datum l E) Y).app M).app (op n)) ≫
            (a.hom.app M).app (op n) =
          ((completedReductionModuleUnit (datum l E) X).app ((pullR l E g).obj M)).app
            (op n)) ∧
      (∀ (M : modules l E Y) (n : ℕ),
        (res l E X).map ((pullR l E g).map
            (((completedReductionModuleUnit (datum l E) Y).app M).app (op n))) ≫
            ((theta l E g d).hom.app M).app (op n) =
          d.hom.app M ≫ (pullC l E g).map
            (((OrderedExchange.ordinaryAugmentation (datum l E) Y).app
              ((res l E Y).obj M)).app (op n))) ∧
      (∀ (M : modules l E Y) (n : ℕ),
        (pullC l E g).map
            (((OrderedExchange.ordinaryAugmentation (datum l E) Y).app
              ((res l E Y).obj M)).app (op n)) ≫
            (c.hom.app M).app (op n) =
          ((OrderedExchange.ordinaryAugmentation (datum l E) X).app
            ((pullC l E g).obj ((res l E Y).obj M))).app (op n)) := by
  constructor
  · intro W _ H j n
    exact commonQuotient l E W (H.X j) n
  · obtain ⟨a, ha⟩ := completedTowerComparison l E g
    obtain ⟨c, hc⟩ := constantTowerComparison l E g
    exact ⟨sourceComparison l E g, a, c, sourceComparison_normalized l E g,
      completed_tensor l E g a ha, ha, theta_augmentation l E g (sourceComparison l E g),
      hc⟩

end WeilConjectures.IntegralAugmentedQuotient
