/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedOpenEndpointLimitTransport
public import Sheaf.Paper.OrderedExchangeCoefficientComparison
public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
public import Sheaf.Paper.SfCbcExtensionZeroCompletion
public import Sheaf.Paper.CompletedPullbackUnitTower
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
import Sheaf.Paper.SupportProperUnitNormalization
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows

/-! # The completed intermediate compact-support object

Source: main-20261015, thm-cbc-complete-proetale, final compatibility paragraph;
Stacks Tags 099M, 099N, 03DI, 03DJ and 0A07
(blueprint: lem-cbc-completed-support-intermediate-tower).

All tower morphisms are defined before evaluation. Completion follows the ordinary
compact-support functor; ordinary extension is never asserted to preserve completeness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower
open AlgebraicGeometry.ProEtale.StrictTower
open OrderedExchange

attribute [local irreducible] proEtaleConstantInverseImageMap

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Ordinary derived extension, using the localized open adjunction.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-completed-support-intermediate-tower). -/
abbrev openExtension {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] :=
  (moduleJ A j).mapDerivedCategory

/-- The exact open adjunction retains the ordinary open unit.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def openAdjunction {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] :
    openExtension (A := A) j ⊣ pull (A := A) j :=
  ((moduleJAdj A j).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    (modulePullback A j).rightDerivedFunctorIsoMapDerivedCategory

/-- Strict extension/tensor comparison, defined as the open-unit mate of pullback/tensor.
Source: Stacks 03DI, 06YY (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def openTensor {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] :
    reduction d X ⋙ J A j ⟶ openExtension (A := A) j ⋙ reduction d U :=
  (mateEquiv (openAdjunction (A := A) j) (jAdj A j)).symm
    (reductionPullIso d j).inv

/-- The strict proper projection is the counit-tensor adjunct, with no input restriction.
Source: Stacks 0B56, 099M (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def properProjection {U Y : Scheme.{t}} (p : U ⟶ Y) :
    push (A := A) p ⋙ reduction d Y ⟶ reduction d U ⋙ R A p :=
  mateEquiv (proEtaleRingDerivedAdjunction p (exchangeConstantRing Y A)
    (exchangeConstantRing U A) (exchangeConstantIso p A))
    (adj A p) (reductionPullIso d p).hom

/-- Ordinary compact support for the supplied open/proper factorization.
Source: blueprint, definition of B_f
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ordinary {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y) [IsOpenImmersion j] :=
  openExtension (A := A) j ⋙ push (A := A) p

/-- The actual strict-tower compact-support operation F_f.
Source: blueprint, definition of F_f
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def tower {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y) [IsOpenImmersion j] :=
  J A j ⋙ R A p

/-- Completed compact support C_Y B_f on the ambient constant-coefficient category.
Source: blueprint, definition of widehat B_f
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def completed {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y) [IsOpenImmersion j] :=
  ordinary (A := A) j p ⋙ completion d Y

/-- Open tensor descent and reduction of the completion unit are invertible as strict maps.
Source: Stacks 03DI, 06YY, 099M; node proof Steps 2, 3 and 8.
Proof: extend one flat-term K-flat representative. Exact restriction and extension,
with their projection formula, preserve its flatness and K-flatness. The mate is the
balanced tensor map on every term, hence an isomorphism of strict complexes. Quotient
completion is the reflector of Stacks 099M; its unit becomes invertible after quotient
reduction, by the unit-normalized completed-pullback theorem. These are strict maps,
not a lifting of unrelated evaluated maps.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem strictUnits {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] :
    IsIso (openTensor d j) ∧
      IsIso (whiskerRight (unit d U) (reduction d U)) := by
  sorry

/-- The strict tensor comparison as an isomorphism, fixed by its open-unit mate.
Source: Stacks 03DI, 06YY (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def openTensorIso {X U : Scheme.{t}} (j : X ⟶ U) [IsOpenImmersion j] :=
  @asIso _ _ _ _ (openTensor d j) (strictUnits d j).1

/-- The counit projection followed by the strict open tensor comparison: t_f.
Source: blueprint, displayed normalization for theta
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ordinaryReduction {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] :
    ordinary (A := A) j p ⋙ reduction d Y ⟶ reduction d X ⋙ tower (A := A) j p :=
  whiskerLeft (openExtension (A := A) j) (properProjection d p) ≫
    whiskerRight (openTensorIso d j).inv (R A p)

/-- Reduction of the specified target completion unit, for the actual B_f.
Source: Stacks 099M (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def reducedUnit {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] :
    ordinary (A := A) j p ⋙ reduction d Y ⟶ completed d j p ⋙ reduction d Y :=
  whiskerLeft (ordinary (A := A) j p) (whiskerRight (unit d Y) (reduction d Y))

/-- Strict theta is t_f after the inverse reduced completion unit.
Source: blueprint, theta equation (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def theta {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y) [IsOpenImmersion j] :
    completed d j p ⋙ reduction d Y ⟶ reduction d X ⋙ tower (A := A) j p :=
  letI := (strictUnits d (𝟙 Y)).2
  letI : IsIso (reducedUnit d j p) := by
    unfold reducedUnit
    infer_instance
  CategoryTheory.inv (reducedUnit d j p) ≫ ordinaryReduction d j p

/-- The normalized reconstruction mu=L(theta) eta, as a natural transformation.
Source: blueprint, mu equation (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def mu {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y) [IsOpenImmersion j] :
    completed d j p ⟶ reduction d X ⋙ tower (A := A) j p ⋙ rlim (A := A) Y :=
  whiskerLeft (completed d j p) (unit d Y) ≫
    whiskerRight (theta d j p) (rlim (A := A) Y)


/-- Completion of the ordinary open unit, then cancellation of the complete proper target.
Source: Stacks 099M, 099N, node proof Steps 2--4.
Proof: reduction of the completion unit is invertible. The perfect-quotient projection
formula makes its proper direct image a reduction isomorphism. Completion inverts it;
proper direct image preserves complete objects, so its target unit is invertible.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem completionUnits {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsProper p] :
    IsIso (whiskerRight
      (whiskerRight (whiskerLeft (openExtension (A := A) j) (unit d U))
        (push (A := A) p)) (completion d Y)) ∧
    IsIso (whiskerLeft (openExtension (A := A) j ⋙ completion d U ⋙ push (A := A) p)
      (unit d Y)) ∧ IsIso (theta d j p) ∧ IsIso (mu d j p) ∧
    (∀ K : D (A := A) X, IsComplete d Y ((completed d j p).obj K)) := by
  sorry

/-- The first displayed intermediate identification, defined by the two completion units.
Source: Stacks 099N (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def properCompletedOpen {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsProper p] :
    completed d j p ⟶ openExtension (A := A) j ⋙ completion d U ⋙ push (A := A) p :=
  let a := whiskerRight
    (whiskerRight (whiskerLeft (openExtension (A := A) j) (unit d U))
      (push (A := A) p)) (completion d Y)
  let b := whiskerLeft (openExtension (A := A) j ⋙ completion d U ⋙ push (A := A) p)
    (unit d Y)
  letI : IsIso b := (completionUnits d j p).2.1
  a ≫ CategoryTheory.inv b

/-- The second displayed identification uses open tensor descent, then the normalized
proper direct-image/limit isomorphism. Source: Stacks 0A07, 099N
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def limitCompletedOpen {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] :
    openExtension (A := A) j ⋙ completion d U ⋙ push (A := A) p ⟶
      reduction d X ⋙ tower (A := A) j p ⋙ rlim (A := A) Y :=
  whiskerRight (whiskerRight (openTensorIso d j).inv (rlim (A := A) U))
      (push (A := A) p) ≫
    whiskerLeft (reduction d X ⋙ J A j) (directLimitIso (A := A) p).hom

private theorem unit_precomp_injective {C : Type*} [Category C]
    (F : C ⥤ C) (η : 𝟭 C ⟶ F) {B T : C}
    [IsIso (F.map (η.app B))] [IsIso (η.app T)]
    {f g : F.obj B ⟶ T} (h : η.app B ≫ f = η.app B ≫ g) : f = g := by
  have hm := congrArg F.map h
  simp only [Functor.map_comp] at hm
  have hf : F.map f = F.map g := (cancel_epi (F.map (η.app B))).mp hm
  apply (cancel_mono (η.app T)).mp
  calc
    f ≫ η.app T = η.app (F.obj B) ≫ F.map f := η.naturality f
    _ = η.app (F.obj B) ≫ F.map g := congrArg (fun z ↦ η.app (F.obj B) ≫ z) hf
    _ = g ≫ η.app T := (η.naturality g).symm

section Reconstruction

/-- Strict normalization and the actual composite mu, rather than equality of projections.
Source: Stacks 099M, 0A07, node proof Step 4.
Proof: naturality of the diagram-site projection and of the open tensor map gives the
first equation. Write eta as L(augmentation) after the diagonal-limit unit. At the unit
coefficient the counit-tensor projection is identity. Naturality in the augmentation,
and the diagonal normalization of directLimitIso, give the second equation strictly.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem reconstructionNormalization {X U Y : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsProper p] :
    reducedUnit d j p ≫ theta d j p = ordinaryReduction d j p ∧
    properCompletedOpen d j p ≫ limitCompletedOpen d j p = mu d j p := by
  constructor
  · have := (strictUnits d (𝟙 Y)).2
    have : IsIso (reducedUnit d j p) := by
      unfold reducedUnit
      infer_instance
    dsimp only [theta]
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  · ext K
    let N := (openExtension (A := A) j).obj K
    let B := (push (A := A) p).obj N
    let E := (push (A := A) p).obj ((completion d U).obj N)
    let T := (rlim (A := A) Y).obj
      ((R A p).obj ((J A j).obj ((reduction d X).obj K)))
    let v : B ⟶ E := (push (A := A) p).map ((unit d U).app N)
    let q := (openTensorIso d j).inv.app K
    have hred := (strictUnits d (𝟙 Y)).2
    have hredB : IsIso ((reduction d Y).map ((unit d Y).app B)) :=
      NatIso.isIso_app_of_isIso (whiskerRight (unit d Y) (reduction d Y)) B
    have hCB : IsIso ((completion d Y).map ((unit d Y).app B)) := by
      change IsIso ((rlim (A := A) Y).map ((reduction d Y).map ((unit d Y).app B)))
      infer_instance
    have hm := (completionUnits d j p).2.2.2.1
    have hc := (completionUnits d j p).2.2.2.2 K
    have hT : IsIso ((unit d Y).app T) := by
      exact (NatTrans.isIso_app_iff_of_iso (unit d Y)
        ((asIso (mu d j p)).app K)).mp hc
    have hb := (completionUnits d j p).2.1
    have hE : IsIso ((unit d Y).app E) :=
      NatIso.isIso_app_of_isIso
        (whiskerLeft (openExtension j ⋙ completion d U ⋙ push p) (unit d Y)) K
    have hp : (properProjection d p).app N = projection d p N := by
      let a := proEtaleRingDerivedAdjunction p (exchangeConstantRing Y A)
        (exchangeConstantRing U A) (exchangeConstantIso p A)
      let b := exchangeTowerAdjunction p (exchangeConstantRing Y A)
        (exchangeConstantRing U A) (exchangeConstantIso p A)
      apply (b.homEquiv _ _).symm.injective
      change (b.homEquiv _ _).symm ((mateEquiv a b
        (TwoSquare.mk _ _ _ _ (reductionPullIso d p).hom)).app N) =
        (b.homEquiv _ _).symm ((b.homEquiv _ _)
          ((reductionPullIso d p).hom.app ((push p).obj N) ≫
            (reduction d U).map (a.counit.app N)))
      rw [Equiv.symm_apply_apply]
      exact mateEquiv_counit a b
        (TwoSquare.mk _ _ _ _ (reductionPullIso d p).hom) N
    have hn : (push p).map ((rlim (A := A) U).map q) ≫
        (directLimitIso (A := A) p).hom.app ((J A j).obj ((reduction d X).obj K)) =
      (directLimitIso (A := A) p).hom.app ((reduction d U).obj N) ≫
        (rlim (A := A) Y).map ((R A p).map q) :=
      (directLimitIso (A := A) p).hom.naturality q
    have hu := supportProperUnitNormalization d p N
    have hv : (unit d Y).app B ≫ (completion d Y).map v =
        v ≫ (unit d Y).app E := ((unit d Y).naturality v).symm
    have hr : (unit d Y).app B ≫ (unit d Y).app ((completion d Y).obj B) =
        (unit d Y).app B ≫ (completion d Y).map ((unit d Y).app B) :=
      (unit d Y).naturality ((unit d Y).app B)
    simp only [properCompletedOpen, limitCompletedOpen, mu, theta, completed,
      ordinary, tower, reducedUnit, ordinaryReduction, NatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app, Functor.comp_obj,
      NatIso.isIso_inv_app]
    change ((completion d Y).map v ≫ inv ((unit d Y).app E)) ≫
        ((push p).map ((rlim (A := A) U).map q) ≫
          (directLimitIso (A := A) p).hom.app ((J A j).obj ((reduction d X).obj K))) =
      (unit d Y).app ((completion d Y).obj B) ≫
        (rlim (A := A) Y).map (inv ((reduction d Y).map ((unit d Y).app B)) ≫
          ((properProjection d p).app N ≫ (R A p).map q))
    apply unit_precomp_injective (completion d Y) (unit d Y) (B := B) (T := T)
    simp only [Category.assoc]
    rw [reassoc_of% hv]
    simp only [IsIso.hom_inv_id_assoc]
    rw [hn, ← Category.assoc, hu, ← hp]
    simp only [Category.assoc]
    rw [reassoc_of% hr]
    simp only [completion, Functor.comp_map, ← Functor.map_comp,
      IsIso.hom_inv_id_assoc]
    rfl

end Reconstruction

/-- Pullback square in the ordinary derived category, with the specified compositors.
Source: Stacks 09AE (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ordinarySquare {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :=
  Functor.mapDerivedCategorySquareIso (moduleSquareG A k r p i h)

/-- Ordinary proper exchange is the square mate under the fixed derived adjunctions.
Source: Stacks 09AE (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ordinaryProperExchange {U Y U' Y' : Scheme.{t}} (u : U' ⟶ U) (p' : U' ⟶ Y')
    (p : U ⟶ Y) (y : Y' ⟶ Y) (h : u ≫ p = p' ≫ y) :
    push (A := A) p ⋙ pull (A := A) y ⟶ pull (A := A) u ⋙ push (A := A) p' :=
  mateEquiv (proEtaleRingDerivedAdjunction p (exchangeConstantRing Y A)
    (exchangeConstantRing U A) (exchangeConstantIso p A))
    (proEtaleRingDerivedAdjunction p' (exchangeConstantRing Y' A)
      (exchangeConstantRing U' A) (exchangeConstantIso p' A))
    (ordinarySquare (A := A) u p' p y h).hom

/-- The inverse ordinary open exchange is the open-unit mate of the square compositor.
Source: Stacks 03DI, 09AE (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ordinaryOpenInverse {X U X' U' : Scheme.{t}} (x : X' ⟶ X) (j' : X' ⟶ U')
    (j : X ⟶ U) (u : U' ⟶ U) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : x ≫ j = j' ≫ u) :
    pull (A := A) x ⋙ openExtension (A := A) j' ⟶
      openExtension (A := A) j ⋙ pull (A := A) u :=
  (mateEquiv (openAdjunction (A := A) j) (openAdjunction (A := A) j')).symm
    (ordinarySquare (A := A) x j' j u h).inv

open AlgebraicGeometry.ProEtale in
private theorem openAdjunction_unit_isIso {X U : Scheme.{t}} (j : X ⟶ U)
    [IsOpenImmersion j] : IsIso (openAdjunction (A := A) j).unit := by
  let C := ModuleCat.{t + 1} A
  have : IsIso (openImmersionLowerShriekAdjunction C j).unit :=
    (openImmersionAdjunctionTriple C j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit C j)
  let ff := (openImmersionLowerShriekAdjunction C j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have := fixedRestriction_full A X
  have := fixedRestriction_faithful A X
  have := fixedRestriction_faithful A U
  have : IsIso (moduleJAdj A j).unit :=
    unit_iso_of_comparison (L := moduleJ A j) (R := modulePullback A j)
      (moduleJAdj A j) _ _ (openImmersionLowerShriek C j) (fixedOpen A j)
  exact exact_unit_iso (moduleJAdj A j) (openAdjunction (A := A) j)

/-- Open base change retains its inverse's unit normalization.
Source: Stacks 09AE.
Proof: identify the open sites with their localized sites. On a pullback square the
extension presheaf sums over the same lifts, so the open-unit mate is invertible.
Exact localization preserves the mate and its inverse, including on the empty open.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem ordinaryOpenInverse_isIso {X U X' U' : Scheme.{t}} (x : X' ⟶ X)
    (j' : X' ⟶ U') (j : X ⟶ U) (u : U' ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : x ≫ j = j' ≫ u)
    (_s : IsPullback x j' j u) : IsIso (ordinaryOpenInverse (A := A) x j' j u h) := by
  have := openAdjunction_unit_isIso (A := A) j
  have := openAdjunction_unit_isIso (A := A) j'
  let ff := (openAdjunction (A := A) j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let e := Functor.mapDerivedCategorySquareIso (moduleOpenSquare A x j' j u _s)
  have hi (M : D (A := A) X) :
      IsIso ((ordinaryOpenInverse (A := A) x j' j u h).app M) := by
    have hc : IsIso ((openAdjunction (A := A) j').counit.app
        ((pull (A := A) u).obj ((openExtension (A := A) j).obj M))) :=
      (openAdjunction (A := A) j').isIso_counit_app_of_iso (e.app M)
    have hu : IsIso ((openAdjunction (A := A) j).unit.app M) := inferInstance
    have he : (ordinaryOpenInverse (A := A) x j' j u h).app M =
        ((openAdjunction (A := A) j').homEquiv _ _).symm
          ((pull (A := A) x).map ((openAdjunction (A := A) j).unit.app M) ≫
            (ordinarySquare (A := A) x j' j u h).inv.app
              ((openExtension (A := A) j).obj M)) := by
      apply ((openAdjunction (A := A) j').homEquiv _ _).injective
      erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
      exact (unit_mateEquiv_symm (openAdjunction (A := A) j)
        (openAdjunction (A := A) j')
        (TwoSquare.mk _ _ _ _ (ordinarySquare (A := A) x j' j u h).inv) M).symm
    rw [he, Adjunction.homEquiv_counit]
    have hs : IsIso ((ordinarySquare (A := A) x j' j u h).inv.app
        ((openExtension (A := A) j).obj M)) := inferInstance
    have hm : IsIso ((pull (A := A) x).map ((openAdjunction (A := A) j).unit.app M)) :=
      inferInstance
    apply IsIso.comp_isIso'
    · apply Functor.map_isIso
    · exact hc
  exact NatIso.isIso_of_isIso_app _

section Exchange
variable {X U Y X' U' Y' : Scheme.{t}}
variable (j : X ⟶ U) (p : U ⟶ Y) (j' : X' ⟶ U') (p' : U' ⟶ Y')
variable (x : X' ⟶ X) (u : U' ⟶ U) (y : Y' ⟶ Y)
variable [IsOpenImmersion j] [IsOpenImmersion j']
variable (hj : x ≫ j = j' ≫ u) (hp : u ≫ p = p' ≫ y)
variable (sj : IsPullback x j' j u)

/-- The specified proper-mate, then proper image of the open-unit mate, before completion.
Source: blueprint ordered exchange (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def ordinaryExchange :
    ordinary (A := A) j p ⋙ pull (A := A) y ⟶
      pull (A := A) x ⋙ ordinary (A := A) j' p' :=
  letI := ordinaryOpenInverse_isIso (A := A) x j' j u hj sj
  whiskerLeft (openExtension (A := A) j)
      (ordinaryProperExchange (A := A) u p' p y hp) ≫
    whiskerRight (CategoryTheory.inv (ordinaryOpenInverse (A := A) x j' j u hj))
      (push (A := A) p')

/-- The corresponding specified strict-tower exchange, before evaluation.
Source: blueprint ordered exchange (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def strictExchange :
    tower (A := A) j p ⋙ G A y ⟶ G A x ⋙ tower (A := A) j' p' :=
  whiskerLeft (J A j) (exchange A u p' p y hp) ≫
    whiskerRight (beta A x j' j u hj sj).hom (R A p')

/-- The source endpoint insertion, obtained from the prescribed completion unit.
Source: Stacks 099M (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def sourceInsertion :
    ordinary (A := A) j p ⋙ completePull d y ⟶ completed d j p ⋙ completePull d y :=
  whiskerRight (whiskerLeft (ordinary (A := A) j p) (unit d Y)) (completePull d y)

/-- The target endpoint insertion completes both the input and the compact support target.
Source: Stacks 099M (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def targetInsertion :
    pull (A := A) x ⋙ completed d j' p' ⟶ completePull d x ⋙ completed d j' p' :=
  whiskerRight (whiskerLeft (pull (A := A) x) (unit d X')) (completed d j' p')

/-- Endpoint insertions are reduction isomorphisms and hence become invertible here.
Source: Stacks 099M, 099N.
Proof: pullback, open tensor descent and the perfect-quotient proper projection preserve
reduction isomorphisms. Both displayed targets are completed, so the completion reflector
makes the unit insertions invertible. This holds on ambient complexes.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem endpointInsertions [QuasiCompact j] [QuasiCompact j'] [IsProper p] [IsProper p'] :
    IsIso (sourceInsertion d j p y) ∧ IsIso (targetInsertion d j' p' x) := by
  have hunit (T : Scheme.{t}) := (strictUnits d (𝟙 T)).2
  constructor
  · let e : completePull d y ≅ reduction d Y ⋙ G A y ⋙ rlim (A := A) Y' :=
      Functor.isoWhiskerRight (reductionPullIso d y).symm (rlim (A := A) Y')
    have hi (K : D (A := A) X) : IsIso ((sourceInsertion d j p y).app K) := by
      let v := (unit d Y).app ((ordinary (A := A) j p).obj K)
      have : IsIso ((reduction d Y).map v) :=
        inferInstanceAs
          (IsIso ((whiskerRight (unit d Y) (reduction d Y)).app
            ((ordinary (A := A) j p).obj K)))
      change IsIso ((completePull d y).map v)
      exact (NatIso.isIso_map_iff e v).2 (by dsimp only [Functor.comp_map]; infer_instance)
    exact NatIso.isIso_of_isIso_app _
  · have := (completionUnits d j' p').2.2.2.1
    let e := asIso (mu d j' p')
    have hi (K : D (A := A) X) : IsIso ((targetInsertion d j' p' x).app K) := by
      let v := (unit d X').app ((pull (A := A) x).obj K)
      have : IsIso ((reduction d X').map v) :=
        inferInstanceAs
          (IsIso ((whiskerRight (unit d X') (reduction d X')).app
            ((pull (A := A) x).obj K)))
      change IsIso ((completed d j' p').map v)
      exact (NatIso.isIso_map_iff e v).2 (by dsimp only [Functor.comp_map]; infer_instance)
    exact NatIso.isIso_of_isIso_app _

/-- Completed ordinary exchange: inverse source unit, completed ordinary exchange,
then the completed target unit. Source: blueprint completed exchange definition
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def completedExchange [QuasiCompact j] [QuasiCompact j'] [IsProper p] [IsProper p'] :
    completed d j p ⋙ completePull d y ⟶ completePull d x ⋙ completed d j' p' :=
  letI := (endpointInsertions d j p j' p' x y).1
  CategoryTheory.inv (sourceInsertion d j p y) ≫
    whiskerRight (ordinaryExchange j p j' p' x u y hj hp sj) (completion d Y') ≫
    targetInsertion d j' p' x

end Exchange


/-- Reduction of completed pullback, fixed by the reduced unit and the strict tensor map.
Source: Stacks 099N(5) (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def pullReduction {V W : Scheme.{t}} (g : V ⟶ W) :
    completePull d g ⋙ reduction d V ⟶ reduction d W ⋙ G A g :=
  let b := whiskerLeft (pull (A := A) g) (whiskerRight (unit d V) (reduction d V))
  letI := (strictUnits d (𝟙 V)).2
  letI : IsIso b := inferInstance
  CategoryTheory.inv b ≫ (reductionPullIso d g).inv

/-- Completed pullback reconstruction before any evaluation.
Source: Stacks 099N(5) (blueprint: lem-cbc-completed-support-intermediate-tower). -/
def pullReconstruction {V W : Scheme.{t}} (g : V ⟶ W) :
    completePull d g ⟶ reduction d W ⋙ G A g ⋙ rlim (A := A) V :=
  whiskerRight (reductionPullIso d g).inv (rlim (A := A) V)

/-- The source identification uses pullback reconstruction followed by strict theta.
Source: blueprint exchange substitution
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def exchangeSource {X U Y Y' : Scheme.{t}} (j : X ⟶ U) (p : U ⟶ Y)
    [IsOpenImmersion j] (y : Y' ⟶ Y) :
    completed d j p ⋙ completePull d y ⟶
      reduction d X ⋙ tower (A := A) j p ⋙ G A y ⋙ rlim (A := A) Y' :=
  whiskerLeft (completed d j p) (pullReconstruction d y) ≫
    whiskerRight (whiskerRight (theta d j p) (G A y)) (rlim (A := A) Y')

/-- The target identification uses mu followed by unit-normalized pullback reduction.
Source: blueprint exchange substitution
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
def exchangeTarget {X X' U' Y' : Scheme.{t}} (j' : X' ⟶ U') (p' : U' ⟶ Y')
    [IsOpenImmersion j'] (x : X' ⟶ X) :
    completePull d x ⋙ completed d j' p' ⟶
      reduction d X ⋙ G A x ⋙ tower (A := A) j' p' ⋙ rlim (A := A) Y' :=
  whiskerLeft (completePull d x) (mu d j' p') ≫
    whiskerRight (whiskerRight (pullReduction d x) (tower (A := A) j' p'))
      (rlim (A := A) Y')

/-- The completed exchange is the limit of the specified strict exchange, with all
endpoint identifications. This is an equality of natural transformations of ambient
complexes, so it includes naturality before evaluation and after any base change.
Source: Stacks 099N, 09AE; node proof Steps 9--11.
Proof: use the unit equation defining pullReduction. On flat-term K-flat complexes,
ordinaryOpenInverse and openTensor are transposes of the same pure-tensor open-unit
square. The proper square is the counit-tensor exchange square, so its reductions
commute with properProjection. Thus ordinaryReduction transports the proper-then-open
composite to strictExchange. Invert the reduced completion units and apply Rlim.
The augmentation-normalized equation for mu identifies both endpoint insertions;
this gives the displayed equality strictly, without inferring it from evaluations.
(blueprint: lem-cbc-completed-support-intermediate-tower). -/
theorem exchangeSubstitution {X U Y X' U' Y' : Scheme.{t}}
    (j : X ⟶ U) (p : U ⟶ Y) (j' : X' ⟶ U') (p' : U' ⟶ Y')
    (x : X' ⟶ X) (u : U' ⟶ U) (y : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion j'] [QuasiCompact j] [QuasiCompact j']
    [IsProper p] [IsProper p'] (hj : x ≫ j = j' ≫ u) (hp : u ≫ p = p' ≫ y)
    (sj : IsPullback x j' j u) (_sp : IsPullback u p' p y) :
    completedExchange d j p j' p' x u y hj hp sj ≫ exchangeTarget d j' p' x =
      exchangeSource d j p y ≫
        whiskerLeft (reduction d X)
          (whiskerRight (strictExchange j p j' p' x u y hj hp sj) (rlim (A := A) Y')) ∧
    IsIso (exchangeSource d j p y) ∧ IsIso (exchangeTarget d j' p' x) ∧
    IsIso (pullReduction d x) := by
  sorry


end AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower
