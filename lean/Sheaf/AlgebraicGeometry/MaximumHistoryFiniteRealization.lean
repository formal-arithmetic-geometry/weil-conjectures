module

public import Sheaf.AlgebraicGeometry.ResolutionInvariantCalculusData
public import Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution
public import Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory
import Sheaf.AlgebraicGeometry.MaximumHistoryLowerCutTower
import Sheaf.AlgebraicGeometry.MaximumHistoryCommonStage

/-! # Finite realization of the maximum-center rule

Source: ILO, Expose VIII, 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13, pp. 91--94;
conditional history argument extracted from embedded ambient comparison
(blueprint: lem-trf-maximum-history-finite-realization).

The calculus is supplied, not constructed. The realization records every prefix,
maximum extension and ideal, and identifies its lower-cut tower with its final history.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open EmbeddedResolutionHistory

/-- The data asserted by the finite-realization lemma, with every clause retained.
`history i` is the prefix after `i` extensions. Labels are positive invariant values
in reverse order, shared by every input; no connectedness or dimension condition occurs.
`cutIndex` counts exactly the labels in a lower cut. Its diagram identifications and
center equations retain actual ideals, including centers with identity intrinsic blowup.
Source: ILO VIII 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13, pp. 91--94
(blueprint: lem-trf-maximum-history-finite-realization). -/
structure MaximumHistoryRealization {V : Type w} [LinearOrder V] [OrderBot V]
    (ν : ResolutionInvariantCalculus.{u} V) (A : EmbeddedResolutionPair.{u}) (r : ℕ) where
  history : ∀ i : Fin (r + 1), EmbeddedResolutionHistory A i.val
  extension : ∀ i : Fin r, Extension (history i.castSucc) (history i.succ)
  admissible : ∀ i, Admissible ν.value (history i)
  nonregular : ∀ i : Fin r, ¬ IsRegularScheme (history i.castSucc).X
  maximum : ∀ i, IsMaximumStep ν.value (extension i)
  label : Fin r → OrderDual {v : V // v ≠ ⊥}
  positive : ∀ i, ⊥ < (label i).val
  greatest : ∀ i, IsGreatest (Set.range (ν.value (history i.castSucc))) (label i).val
  increasing : StrictMono label
  centerGeometry : ∀ i,
    Nonempty ((history i.succ).center (Fin.last i.val)).subscheme ∧
    IsRegularScheme ((history i.succ).center (Fin.last i.val)).subscheme ∧
    interior (Set.range (extension i).centerMap) = ∅ ∧
    ((history i.succ).center (Fin.last i.val)).toModules.IsFiniteTypeWithFiniteTypeKernels ∧
    (extension i).centerMap.ker.toModules.IsFiniteTypeWithFiniteTypeKernels
  intermediateGeometry : ∀ i, Smooth (history i).base ∧ IsSeparated (history i).base ∧
    LocallyOfFiniteType (history i).base ∧ QuasiCompact (history i).base ∧
    IsReduced (history i).X
  finalRegular : IsRegularScheme (history (Fin.last r)).X
  regularInput : IsRegularScheme A.X → r = 0
  emptyInput : IsEmpty A.X → r = 0
  tower : LabeledEmbeddedResolutionTower (OrderDual {v : V // v ≠ ⊥}) A
  activeLabels : ∀ l, l ∈ tower.labels ↔ ∃ i, label i = l
  cutIndex : LowerSet (OrderDual {v : V // v ≠ ⊥}) →o Fin (r + 1)
  cutCount : ∀ D, (cutIndex D).val = Set.ncard {i : Fin r | label i ∈ D}
  cutFirst : cutIndex ⊥ = 0
  cutLast : cutIndex ⊤ = Fin.last r
  cutBefore : ∀ i, cutIndex (LowerSet.Iio (label i)) = i.castSucc
  cutAfter : ∀ i, cutIndex (LowerSet.Iic (label i)) = i.succ
  ambient : tower.ambient ≅ cutIndex.toFunctor.op ⋙ (history (Fin.last r)).ambient
  intrinsic : tower.intrinsic ≅ cutIndex.toFunctor.op ⋙ (history (Fin.last r)).intrinsic
  inclusion : tower.inclusion ≫ ambient.hom =
    intrinsic.hom ≫ Functor.whiskerLeft cutIndex.toFunctor.op (history (Fin.last r)).inclusion
  initialAmbient : (ambient.app (op ⊥)).hom ≫
    eqToHom (congrArg (fun i ↦ (history (Fin.last r)).ambient.obj (op i)) cutFirst) ≫
      (history (Fin.last r)).initialAmbient.hom = tower.initialAmbient.hom
  initialIntrinsic : (intrinsic.app (op ⊥)).hom ≫
    eqToHom (congrArg (fun i ↦ (history (Fin.last r)).intrinsic.obj (op i)) cutFirst) ≫
      (history (Fin.last r)).initialIntrinsic.hom = tower.initialIntrinsic.hom
  ambientCenters : ∀ i, tower.center (label i) =
    ((history (Fin.last r)).center i).comap
      ((ambient.app (op (LowerSet.Iio (label i)))).hom ≫
        eqToHom (congrArg (fun j ↦ (history (Fin.last r)).ambient.obj (op j)) (cutBefore i)))
  intrinsicCenters : ∀ i, (tower.centerToIntrinsic (label i)).ker =
    ((history (Fin.last r)).centerToIntrinsic i).ker.comap
      ((intrinsic.app (op (LowerSet.Iio (label i)))).hom ≫
        eqToHom (congrArg (fun j ↦ (history (Fin.last r)).intrinsic.obj (op j)) (cutBefore i)))
  inactiveAmbient : ∀ l, l ∉ tower.labels →
    cutIndex (LowerSet.Iio l) = cutIndex (LowerSet.Iic l)

/-- A supplied terminating calculus has a finite realization, with uniquely determined
length, stopping at the first regular strict transform. No well-foundedness of `V` is used.
Source: ILO VIII 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13, pp. 91--94
(blueprint: lem-trf-maximum-history-finite-realization).

Proof: start with an empty history. At every nonregular final transform use
`maximumExists`; `maximumGeometry` gives its nonempty regular nowhere dense coherent
center, and `nextGeometry` gives the next embedded rational pair. If this never stops,
countable dependent choice gives the infinite maximum-extension chain forbidden by
`termination`. Stop at the least regular stage; in particular empty and regular inputs
stop immediately, with no exceptional-divisor cleanup. `strictProgress` makes the positive
maxima strictly decrease, hence their reverse-order labels strictly increase. On a finite
disjoint union the same `value` and full maximum on that entire pair are used.
For a lower cut count its active labels: strict increase makes these a prefix. Reindex the
final history by that prefix count, retaining all recorded ideals. At inactive labels the
count is constant, the center ideal is the unit ideal, and the transition is an identity
under the diagram identifications; the invertible-center blowup theorem identifies this
with the ordinary unit-ideal blowup. At active labels use the recorded blowup and strict
transform. The canonical comparison induction in `maximumHistoryRealization_comparison`
identifies any two such histories, and regularity is preserved, so their lengths agree. -/
theorem maximumHistory_finite_realization {V : Type w} [LinearOrder V] [OrderBot V]
    (ν : ResolutionInvariantCalculus.{u} V) (A : EmbeddedResolutionPair.{u}) :
    ∃! r : ℕ, Nonempty (MaximumHistoryRealization ν A r) := by
  obtain ⟨r, ⟨S⟩⟩ := maximumHistoryChronology_exists ν A
  obtain ⟨C⟩ := maximumHistoryChronology_lowerCutTower S
  have hreal : Nonempty (MaximumHistoryRealization ν A r) := ⟨{
    history := S.history
    extension := S.extension
    admissible := S.admissible
    nonregular := S.nonregular
    maximum := S.maximum
    label := S.label
    positive := S.positive
    greatest := S.greatest
    increasing := S.increasing
    centerGeometry := S.centerGeometry
    intermediateGeometry := S.intermediateGeometry
    finalRegular := S.finalRegular
    regularInput := S.regularInput
    emptyInput := S.emptyInput
    tower := C.tower
    activeLabels := C.activeLabels
    cutIndex := C.cutIndex
    cutCount := C.cutCount
    cutFirst := C.cutFirst
    cutLast := C.cutLast
    cutBefore := C.cutBefore
    cutAfter := C.cutAfter
    ambient := C.ambient
    intrinsic := C.intrinsic
    inclusion := C.inclusion
    initialAmbient := C.initialAmbient
    initialIntrinsic := C.initialIntrinsic
    ambientCenters := C.ambientCenters
    intrinsicCenters := C.intrinsicCenters
    inactiveAmbient := C.inactiveAmbient
  }⟩
  refine ⟨r, hreal, ?_⟩
  rintro s ⟨T⟩
  let P : MaximumHistorySegment ν A r := {
    history := S.history
    extension := S.extension
    admissible := S.admissible
    nonregular := S.nonregular
    maximum := S.maximum }
  let Q : MaximumHistorySegment ν A s := {
    history := T.history
    extension := T.extension
    admissible := T.admissible
    nonregular := T.nonregular
    maximum := T.maximum }
  have hr : r ≤ s := by
    by_contra h
    have hs : s < r := Nat.lt_of_not_ge h
    exact S.nonregular ⟨s, hs⟩
      ((maximumHistorySegment_commonStage P Q s (Nat.le_of_lt hs) le_rfl).mpr
        T.finalRegular)
  have hs : s ≤ r := by
    by_contra h
    have ht : r < s := Nat.lt_of_not_ge h
    exact T.nonregular ⟨r, ht⟩
      ((maximumHistorySegment_commonStage P Q r le_rfl (Nat.le_of_lt ht)).mp
        S.finalRegular)
  exact Nat.le_antisymm hs hr

/-- Realizations of the same maximum-center rule are identified by the unique pair of
ambient and intrinsic diagram isomorphisms over their given initial pair, preserving all
center ideals and their order. Thus these are the canonical ordinary blowup comparisons.
Source: ILO VIII 2.1.1--2.1.4, 2.3.4, 2.3.11, pp. 86--87, 91--93
(blueprint: lem-trf-maximum-history-finite-realization).

Proof: identify the initial pairs by the identity. At each subsequent stage smooth-value
compatibility over this identity identifies the greatest values and their full loci.
Reduced closed subschemes with a fixed support have the same radical ideal on every
affine open. Thus the intrinsic and ambient center ideals agree. Principalization makes
the extended center ideal invertible on each ordinary blowup, so the blowup universal
property gives inverse canonical comparison maps, unique over the previous stage.
The scheme-theoretic strict transforms agree because isomorphisms preserve the open locus
and its scheme-theoretic closure. Induct on stages, retaining every center ideal even if
its intrinsic blowup is an identity. Naturality and the initial normalization follow by
construction. Uniqueness follows from blowup uniqueness, and from the closed immersions
of the strict transforms. This also proves independence of the representatives chosen. -/
theorem maximumHistoryRealization_comparison {V : Type w} [LinearOrder V] [OrderBot V]
    {ν : ResolutionInvariantCalculus.{u} V} {A : EmbeddedResolutionPair.{u}} {r : ℕ}
    (T U : MaximumHistoryRealization ν A r) :
    T.label = U.label ∧
    ∃! e : ((T.history (Fin.last r)).ambient ≅ (U.history (Fin.last r)).ambient) ×
        ((T.history (Fin.last r)).intrinsic ≅ (U.history (Fin.last r)).intrinsic),
      (e.1.app (op 0)).hom ≫ (U.history (Fin.last r)).initialAmbient.hom =
        (T.history (Fin.last r)).initialAmbient.hom ∧
      (e.2.app (op 0)).hom ≫ (U.history (Fin.last r)).initialIntrinsic.hom =
        (T.history (Fin.last r)).initialIntrinsic.hom ∧
      (T.history (Fin.last r)).inclusion ≫ e.1.hom =
        e.2.hom ≫ (U.history (Fin.last r)).inclusion ∧
      (∀ i : Fin r, (T.history (Fin.last r)).center i =
        ((U.history (Fin.last r)).center i).comap (e.1.app (op i.castSucc)).hom) ∧
      (∀ i : Fin r, ((T.history (Fin.last r)).centerToIntrinsic i).ker =
        ((U.history (Fin.last r)).centerToIntrinsic i).ker.comap
          (e.2.app (op i.castSucc)).hom) := by
  sorry

end AlgebraicGeometry
