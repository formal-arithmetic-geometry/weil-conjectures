/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.InjectiveTowerRoosShifts
import Sheaf.SixFunctors.IntegralRealizationRecursion
import Sheaf.SixFunctors.RealizationAdjunctionInsertionShift
import Sheaf.Paper.SystemPushforwardRestrictionTransition

/-! # The actual compact-support tower and its fixed Roos shift

Source: blueprint, sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
coefficient-comparison sentence; agent assembly, adic transport Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model).

The tower is restriction of the actual semilinear J-then-S output. Its finite
comparison uses the specified evaluation maps and reduction comparison. Positive
level n+1 is indexed by n. No cone on a diagram in a derived category is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.CompactSupportStrictRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The unary compact-support expression on one independently supplied input.
Source: blueprint coefficient-comparison sentence, assembly Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def expression {B : Scheme.{u}} {X W : Over B} (f : X ⟶ W)
    (c : Compactification f.left) : Expression B PUnit.{u + 1} (fun _ ↦ X) W :=
  .compactSupport f c (.var PUnit.unit)

/-- The actual semilinear output functor S_p J_j R, before total limit.
Source: blueprint coefficient-comparison sentence, assembly Step 1
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def systemOutput (o : Operations l E) {X W : Scheme.{u}} {f : X ⟶ W}
    (c : Compactification f) : Integral l E X ⥤ System l E W :=
  (calculus l E X).reduction ⋙ Operations.shriek l E o c.i ⋙ Operations.push l E o c.g

/-- T_K is obtained by actual exact termwise restriction, including its transitions.
Source: blueprint coefficient-comparison sentence, assembly Step 1
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def tower (o : Operations l E) {X W : Scheme.{u}} {f : X ⟶ W}
    (c : Compactification f) :=
  systemOutput l E o c ⋙ coefficientSequenceDerivedRestriction l E W

/-- Canonical finite evaluation of T_K: restriction, proper/open evaluation, reduction.
Source: blueprint coefficient-comparison sentence, assembly Step 1
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def evaluation (o : Operations l E) {X W : Scheme.{u}} {f : X ⟶ W}
    (c : Compactification f) (n : ℕ) :
    tower l E o c ⋙ coefficientConstantTowerEvaluation l E W n ≅
      compactSupportRestrictedLevel l E c n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (systemOutput l E o c)
      (coefficientRestrictedEvaluationIso l E W n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (calculus l E X).reduction (supportEvaluation l E o c n) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((calculus l E X).reductionEvaluation n) _) _

/-- Source compact support is L S_p J_j R on the ambient integral category.
Source: blueprint coefficient-comparison sentence, assembly Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def source (o : Operations l E) {X W : Scheme.{u}} {f : X ⟶ W}
    (c : Compactification f) := systemOutput l E o c ⋙ coefficientSequenceLimit l E W

/-- The source shift is the specified reduction mate, then exact open shift,
proper adjunction mate, and exact-restriction/right-derived-limit shift. Its
CommShift structure retains zero and addition coherence for all integers.
Source: blueprint coefficient-comparison sentence, assembly Steps 3--4
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
@[instance_reducible]
def sourceShifts (o : Operations l E) {X W : Scheme.{u}} {f : X ⟶ W}
    (c : Compactification f) : (source l E o c).CommShift ℤ := by
  letI := reductionShift l E X
  letI := systemOpenShift l E o c.i
  letI := systemPushShift l E o c.g
  letI := limitShift l E W
  dsimp [source, systemOutput]
  infer_instance

/-- The stipulated complete, constructible, normalized common-bound input domain,
including every intermediate system and compatible etale-origin witnesses.
Source: blueprint coefficient-comparison sentence, assembly Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def allowed (o : Operations l E) {B : Scheme.{u}} {X W : Over B}
    (f : X ⟶ W) (c : Compactification f.left) (K : Integral l E X.left) : Prop :=
  (expression f c).domain l E o (fun _ ↦ K)

/-- The specified c_(S_p J_j), with the recorded integral proper/open endpoint.
Source: blueprint coefficient-comparison sentence, assembly Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def comparison {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X W : Over (Spec (.of D.k))} (f : X ⟶ W)
    (c : Compactification f.left) (g : (expression f c).geometric)
    (K : Integral l E X.left) (hK : allowed l E o f c K) :
    (source l E o c).obj K ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K :=
  (R.comparison (expression f c) g).hom.app ⟨fun _ ↦ K, hK⟩

/-- Identification with the recorded integral functor, fixed by its actual
compact-support finite-reduction projections. Geometric and domain instances are
extracted from the published predicates, rather than imposed again as assumptions.
Source: blueprint coefficient-comparison sentence, assembly Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def RecordedIdentification {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (hl : l ≠ D.p) (R : Realizations l E D o)
    {X W : Over (Spec (.of D.k))} (f : X ⟶ W)
    (c : Compactification f.left) (g : (expression f c).geometric)
    (K : Integral l E X.left) (hK : allowed l E o f c K) : Prop :=
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := g.2.2.2.2.2.1
  letI : QuasiCompact (X.left ↘ Spec (.of D.k)) := g.2.2.2.2.2.2.1
  letI : LocallyOfFiniteType (W.left ↘ Spec (.of D.k)) := g.1
  letI : QuasiCompact (W.left ↘ Spec (.of D.k)) := g.2.1
  letI : IsSeparated f.left := g.2.2.1
  letI : LocallyOfFiniteType f.left := g.2.2.2.1
  letI : QuasiCompact f.left := g.2.2.2.2.1
  ∀ n : ℕ,
    comparison l E R f c g K hK ≫
        (sfQcqsCompactSupportRealization (X := X.left) (Y := W.left) l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
            ⟨K, (hK.1 PUnit.unit).1⟩ ≫
        (derivedScalarExtensionRestrictionAdjunction l E W.left n).choose.unit.app _ ≫
        (scalarReductionDerivedRestriction l E W.left n).map
          (sfCompactSupportFiniteReductionIso (X := X.left) (Y := W.left) l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E
              ⟨K, (hK.1 PUnit.unit).1⟩ n).hom =
      (coefficientConstantTowerProjection l E W.left n).app ((tower l E o c).obj K) ≫
        (evaluation l E o c n).hom.app K

/-- Agreement of the actual compact-support structural maps with their integral
counterparts, including proper/open compositors and finite outer contexts. These
are the published canonical pairs of maps, not equalities detected by evaluation.
Source: blueprint coefficient-comparison sentence, assembly Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def StructuralMaps {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X W : Over (Spec (.of D.k))} (f : X ⟶ W)
    (c : Compactification f.left) (g : (expression f c).geometric) : Prop :=
  ∀ (t : Expression _ PUnit.{u + 1} (fun _ ↦ X) W) (gt : t.geometric)
    (K : Integral l E X.left) (hK : allowed l E o f c K)
    (ht : t.domain l E o (fun _ ↦ K))
    (s : (systemOutput l E o c).obj K ⟶
      t.systemObj l E o ((inputReduction l E (fun _ : PUnit.{u + 1} ↦ X)).obj (fun _ ↦ K)))
    (v : (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj (fun _ ↦ K)),
    CanonicalPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
      R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
      ((inputReduction l E (fun _ : PUnit.{u + 1} ↦ X)).obj (fun _ ↦ K)) (fun _ ↦ K)
      (expression f c) t s v →
    (coefficientSequenceLimit l E W.left).map s ≫
        (R.comparison t gt).hom.app ⟨fun _ ↦ K, ht⟩ =
      comparison l E R f c g K hK ≫ v

/-- Equality with the signed product/cone comparison on the actual restricted
strict system complex. The beta and delta arguments are pinned by their representative
formulas, and the bridge is normalized on simultaneous K-injectives.
Source: blueprint coefficient-comparison sentence, assembly Step 3; Stacks 0941
(blueprint: lem-pur-compact-support-strict-roos-shift-model). -/
def RoosShiftEquation (W : Scheme.{u}) (ρ : IntegralComparisonRoosModel l E W)
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ) (α : D ≅ C⟦r⟧)
    (β : restrictedTower l E W D ≅ restrictedTower l E W C ⋙
      shiftFunctor (CochainComplex (scalarReductionSource l E W) ℤ) r)
    (_hβ : ∀ n : ℕ, (β.hom.app (op n)) =
      ((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).map α.hom ≫
        (((levelRestriction l E W n).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app C)
    (δ : CochainComplex.mappingCone (completedTensorShiftOneSub (restrictedTower l E W D)) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub (restrictedTower l E W C)))⟦r⟧)
    (_hδ : completedTensorShiftConeFormula
      (restrictedTower l E W C) (restrictedTower l E W D) r β δ) : Prop :=
    (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map α.hom) ≫
        (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app C) ≫
        (Functor.commShiftIso (coefficientSequenceLimit l E W)
          (self := limitShift l E W) r).hom.app (DerivedCategory.Q.obj C) ≫
        (shiftFunctor (Integral l E W) r).map
          (integralComparisonRoosBridge l E W ρ C).hom =
      (integralComparisonRoosBridge l E W ρ D).hom ≫
        DerivedCategory.Q.map
          (completedTensorShiftRoosIso (restrictedTower l E W C)
            (restrictedTower l E W D) r δ).hom ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (integralOperationsRoos (restrictedTower l E W C))

/-- The actual restricted tower has the defining compact-support quotient transitions,
and the specified realization is natural and commutes with every fixed integer shift.
The integral shift is the completed proper/open composite; its canonical realization
in the recorded Rf_! functor is sfQcqsCompactSupportRealization.
Source: blueprint coefficient-comparison sentence, adic transport Step 2
(blueprint: lem-pur-compact-support-strict-roos-shift-model).

Proof:
1. On the single K-flat reduction model, finite evaluation is derived quotient
reduction with its actual quotient maps. Exact J_j applies termwise. The system
pushforward restriction-transition theorem gives Rp_(m)* of that map followed
by its canonical coefficient-restriction comparison. Composing with the open
comparison is exactly compactSupportRestrictedTransition. Restriction along the
completed-ring projection composes with quotient restriction. This proves the
transition equation for every m>=n, including identities and composites.
2. Apply the supplied simultaneous realization to S_p J_j. Its comparison is the
specified c, not a new isomorphism. The realization's finite normalization and
canonical-map coherence identify the compact-support projections and structural
maps; its integral endpoint is the proper/open presentation identified with the
recorded integral functor by sfQcqsCompactSupportRealization. Naturality of that
same supplied comparison gives the displayed whole-input naturality equation.
3. Use a simultaneous K-injective strict-tower resolution. The Roos comparison
is the ordinary limit tuple in the product coordinate and zero in the shifted
coordinate. Product reindexing and the signed cone comparison therefore commute
with its kernel inclusion. limitShift_roos gives the same comparison on every
actual strict output representative, retaining its transition maps and projections.
4. The realization recursion writes c_(S J) as properA after proper image of
openA and the inverse reconstruction unit. The insertion-shift theorem gives
the three squares. Compose them and cancel adjacent intermediate comparisons to
obtain the displayed square. The input domain is shift-stable: completeness,
constructibility, origins and normalized transitions are preserved, and finite
cohomological/Tor bounds translate uniformly. The fixed CommShift structures give
zero, addition and inverse coherence. Both product and cone signs multiply under
successive shifts, including negative shifts. No cone in a derived diagram category
or exactness of arbitrary products of module sheaves is used. -/
theorem compactSupportStrictRoosShiftModel
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (o : Operations l E)
    (R : Realizations l E D o) {X W : Over (Spec (.of D.k))} (f : X ⟶ W)
    (c : Compactification f.left) (g : (expression f c).geometric) :
    (∀ (K : Integral l E X.left) (_hK : allowed l E o f c K)
      (m n : ℕ) (h : n ≤ m),
      (pbcTowerTransition W.left (completedIntegralCommRingSheafUnrestricted l E W.left)
          m n h).app ((tower l E o c).obj K) ≫ (evaluation l E o c n).hom.app K =
        (evaluation l E o c m).hom.app K ≫
          compactSupportRestrictedTransition l E c m n h K) ∧
    (∀ (K N : Integral l E X.left) (a : K ⟶ N)
      (hK : allowed l E o f c K) (hN : allowed l E o f c N),
      (source l E o c).map a ≫ comparison l E R f c g N hN =
        comparison l E R f c g K hK ≫
          (PurCompactSupport.image (PurCompactSupport.completed l E) c).map a) ∧
    (∀ (K : Integral l E X.left) (hK : allowed l E o f c K) (r : ℤ),
      ∃ hShift : allowed l E o f c (K⟦r⟧),
        comparison l E R f c g (K⟦r⟧) hShift ≫
            (Functor.commShiftIso _
              (self := (integralShifts l E).compactSupport f.left c) r).hom.app K =
          (Functor.commShiftIso _ (self := sourceShifts l E o c) r).hom.app K ≫
            (comparison l E R f c g K hK)⟦r⟧') ∧
    (∀ (K : Integral l E X.left) (_hK : allowed l E o f c K)
      (C : CochainComplex (coefficientSequenceModules l E W.left) ℤ)
      (_ε : DerivedCategory.Q.obj C ≅ (systemOutput l E o c).obj K)
      (ρ : IntegralComparisonRoosModel l E W.left)
      (CShift : CochainComplex (coefficientSequenceModules l E W.left) ℤ)
      (r : ℤ) (α : CShift ≅ C⟦r⟧)
      (β : restrictedTower l E W.left CShift ≅ restrictedTower l E W.left C ⋙
        shiftFunctor (CochainComplex (scalarReductionSource l E W.left) ℤ) r)
      (hβ : ∀ n : ℕ, β.hom.app (op n) =
        ((levelRestriction l E W.left n).mapHomologicalComplex (.up ℤ)).map α.hom ≫
          (((levelRestriction l E W.left n).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
            C)
      (δ : CochainComplex.mappingCone
          (completedTensorShiftOneSub (restrictedTower l E W.left CShift)) ≅
        (CochainComplex.mappingCone
          (completedTensorShiftOneSub (restrictedTower l E W.left C)))⟦r⟧)
      (hδ : completedTensorShiftConeFormula
        (restrictedTower l E W.left C) (restrictedTower l E W.left CShift) r β δ),
      RoosShiftEquation l E W.left ρ C CShift r α β hβ δ hδ) ∧
    (∀ (K : Integral l E X.left) (hK : allowed l E o f c K),
      IsIso (comparison l E R f c g K hK) ∧ RecordedIdentification l E hl R f c g K hK) ∧
    StructuralMaps l E R f c g := by
  sorry

end WeilConjectures.IntegralSystemRealization.CompactSupportStrictRoos
