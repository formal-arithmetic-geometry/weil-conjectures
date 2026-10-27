/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

import Sheaf.AlgebraicGeometry.ResolutionWordMaximumCenterDescent
import Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry
import Sheaf.AlgebraicGeometry.LocallyClosedStratumSeparatedFiniteType
import Sheaf.AlgebraicGeometry.StrictTransformFlatBaseChange
import WeilConjectures.Blowup.Complement
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Smooth and intrinsic comparison of finite resolution-word histories

Source: ILO VIII 2.3.5(i), 2.3.11--2.3.13, pp. 92--94, referring to BMT sections
6.1--6.3 (blueprint: lem-trf-resolution-word-finite-history-comparison).

Prefixes retain actual center ideals, including stages whose intrinsic blowup is an
identity. Values and strata are compared at every stage, before any termination assertion.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- Truncate a raw history after stage `j`, retaining every preceding center and map.
Source: ILO VIII 2.3.1 and 2.3.4
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def wordPrefix {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) (j : Fin (n + 1)) :
    EmbeddedResolutionHistory A j.val :=
  let h : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  let F := (Fin.castLEOrderEmb (Nat.add_le_add_right h 1)).monotone.functor.op
  { ambient := F ⋙ H.ambient
    intrinsic := F ⋙ H.intrinsic
    inclusion := Functor.whiskerLeft F H.inclusion
    closed := fun k ↦ H.closed (Fin.castLE (Nat.add_le_add_right h 1) k)
    initialAmbient := H.initialAmbient
    initialIntrinsic := H.initialIntrinsic
    initialInclusion := H.initialInclusion
    center := fun k ↦ H.center (Fin.castLE h k)
    centerToIntrinsic := fun k ↦ H.centerToIntrinsic (Fin.castLE h k)
    centerClosed := fun k ↦ H.centerClosed (Fin.castLE h k)
    centerInclusion := fun k ↦ H.centerInclusion (Fin.castLE h k)
    ambientBlowup := fun k ↦ H.ambientBlowup (Fin.castLE h k)
    ambientBlowupMap := fun k ↦ H.ambientBlowupMap (Fin.castLE h k)
    strictTransform := fun k ↦ H.strictTransform (Fin.castLE h k)
    strictTransformMap := fun k ↦ H.strictTransformMap (Fin.castLE h k)
    strictTransformToSource := fun k ↦ H.strictTransformToSource (Fin.castLE h k) }

/-- Evaluate the simultaneous assignment on the actual prefix at a specified stage.
Source: ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def wordAtStage (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n)
    (j : Fin (n + 1)) : H.intrinsic.obj (op j) → HilbertSamuel.ResolutionWord :=
  ν (H.wordPrefix j)

/-- The rational structure map at any ambient stage is its recorded map to the initial pair.
Source: ILO VIII 2.3.1 and 2.3.11
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def wordStageBase {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) (j : Fin (n + 1)) :
    H.ambient.obj (op j) ⟶ Spec (.of (ULift.{u} ℚ)) :=
  H.ambient.map (homOfLE (Fin.zero_le j)).op ≫ H.initialAmbient.hom ≫ A.base

/-- The reduced ideal of a closed subset of a strict transform in its ambient scheme.
Source: ILO VIII 2.3.13; Stacks Tag 01J3
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def wordAmbientIdeal {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) (j : Fin (n + 1))
    (T : TopologicalSpace.Closeds (H.intrinsic.obj (op j))) :
    (H.ambient.obj (op j)).IdealSheafData :=
  ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ H.inclusion.app (op j)).ker

/-- The geometry asserted at every stage, rather than assumed in a raw history.
Source: ILO VIII 2.3.11--2.3.13
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def WordHistoryGeometry {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) : Prop :=
  ∀ j : Fin (n + 1), Smooth (H.wordStageBase j) ∧ IsSeparated (H.wordStageBase j) ∧
    LocallyOfFiniteType (H.wordStageBase j) ∧ QuasiCompact (H.wordStageBase j) ∧
    IsReduced (H.intrinsic.obj (op j))

/-- Stagewise word, local head, tail and reduced-stratum ideal equalities for an actual
cartesian comparison. The stratum is maximal only on the original stage, not necessarily
on its pullback. Empty inverse images have unit ideals in both schemes.
Source: ILO VIII 2.3.5(i), 2.3.13; BMT 6.3
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def WordSmoothComparison (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    {f : EmbeddedResolutionSmoothMap A B}
    {H : EmbeddedResolutionHistory A m} {K : EmbeddedResolutionHistory B n}
    (c : SmoothPullback f H K) : Prop :=
  ∀ j : Fin (n + 1),
    (∀ y : H.intrinsic.obj (op (c.index j)),
      wordAtStage ν H (c.index j) y = wordAtStage ν K j (c.intrinsic j y) ∧
      ∃ s : ℕ,
        ringKrullDim (((c.intrinsic j).fiber (c.intrinsic j y)).presheaf.stalk
          ((c.intrinsic j).asFiber y)) = (s : WithBot ℕ∞) ∧
        HilbertSamuel.localFunction (H.intrinsic.obj (op (c.index j))) y =
          (HilbertSamuel.summation^[s])
            (HilbertSamuel.localFunction (K.intrinsic.obj (op j)) (c.intrinsic j y)) ∧
        HilbertSamuel.minimumComponentDimension (H.intrinsic.obj (op (c.index j))) y =
          HilbertSamuel.minimumComponentDimension (K.intrinsic.obj (op j))
            (c.intrinsic j y) + s ∧
        HilbertSamuel.componentDimensionCount (H.intrinsic.obj (op (c.index j))) y =
          HilbertSamuel.componentDimensionCount (K.intrinsic.obj (op j))
            (c.intrinsic j y)) ∧
    (∀ (y : H.intrinsic.obj (op (c.index j)))
      (C : ResolutionWordChart R (H.wordPrefix (c.index j)) y)
      (D : ResolutionWordChart R (K.wordPrefix j) (c.intrinsic j y)), C.tail = D.tail) ∧
    ∀ (v : HilbertSamuel.ResolutionWord)
      (T : TopologicalSpace.Closeds (K.intrinsic.obj (op j))),
      IsGreatest (Set.range (wordAtStage ν K j)) v →
      (T : Set (K.intrinsic.obj (op j))) = {x | wordAtStage ν K j x = v} →
      (Scheme.IdealSheafData.vanishingIdeal T).comap (c.intrinsic j) =
        Scheme.IdealSheafData.vanishingIdeal (T.preimage (c.intrinsic j).continuous) ∧
      (K.wordAmbientIdeal j T).comap (c.ambient j) =
        H.wordAmbientIdeal (c.index j) (T.preimage (c.intrinsic j).continuous) ∧
      ((c.intrinsic j) ⁻¹' (T : Set (K.intrinsic.obj (op j))) = ∅ →
        (Scheme.IdealSheafData.vanishingIdeal T).comap (c.intrinsic j) = ⊤ ∧
        (K.wordAmbientIdeal j T).comap (c.ambient j) = ⊤)

/-- Intrinsic diagram identifications compare words and intrinsic reduced maximum ideals,
without imposing any relation between the two smooth ambient embeddings.
Source: ILO VIII 2.3.13; BMT 6.1 Addendum (3)
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def WordIntrinsicComparison (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    {A B : EmbeddedResolutionPair.{u}} {n : ℕ} {e : A.X ≅ B.X}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory B n}
    (c : IntrinsicComparison e H K) : Prop :=
  ∀ j : Fin (n + 1),
    (∀ x : H.intrinsic.obj (op j),
      wordAtStage ν H j x = wordAtStage ν K j ((c.iso.app (op j)).hom x)) ∧
    ∀ (v : HilbertSamuel.ResolutionWord)
      (T : TopologicalSpace.Closeds (H.intrinsic.obj (op j)))
      (U : TopologicalSpace.Closeds (K.intrinsic.obj (op j))),
      IsGreatest (Set.range (wordAtStage ν H j)) v →
      (T : Set (H.intrinsic.obj (op j))) = {x | wordAtStage ν H j x = v} →
      (U : Set (K.intrinsic.obj (op j))) = {x | wordAtStage ν K j x = v} →
      Scheme.IdealSheafData.vanishingIdeal T =
        (Scheme.IdealSheafData.vanishingIdeal U).comap (c.iso.app (op j)).hom

/-- The final ambient map of the given cartesian comparison, transported by its last index.
Source: ILO VIII 2.3.4 and 2.3.13
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def SmoothPullback.wordFinalAmbientMap {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    {f : EmbeddedResolutionSmoothMap A B}
    {H : EmbeddedResolutionHistory A m} {K : EmbeddedResolutionHistory B n}
    (c : SmoothPullback f H K) : H.P ⟶ K.P :=
  eqToHom (congrArg (fun t ↦ H.ambient.obj (op t)) c.last.symm) ≫ c.ambient (Fin.last n)

/-- Repeated smooth pullback, including open restriction, gives the same deletion map,
final comparison maps, word equality and extensions of each original maximum ideal.
Source: ILO VIII 2.3.4--2.3.5(i), 2.3.13
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def WordPullbackCoherence (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord) : Prop :=
  ∀ {A B C : EmbeddedResolutionPair.{u}} {l m n : ℕ}
    {H : EmbeddedResolutionHistory A l} {K : EmbeddedResolutionHistory B m}
    {L : EmbeddedResolutionHistory C n}
    (f : EmbeddedResolutionSmoothMap A B) (g : EmbeddedResolutionSmoothMap B C)
    (h : EmbeddedResolutionSmoothMap A C)
    (c : SmoothPullback f H K) (d : SmoothPullback g K L) (e : SmoothPullback h H L),
    Admissible ν L → h.ambient = f.ambient ≫ g.ambient →
    h.intrinsic = f.intrinsic ≫ g.intrinsic →
    (∀ j, e.index j = c.index (d.index j)) ∧
    e.finalMap = c.finalMap ≫ d.finalMap ∧
    e.wordFinalAmbientMap = c.wordFinalAmbientMap ≫ d.wordFinalAmbientMap ∧
    (∀ x : H.X, ν H x = ν L ((c.finalMap ≫ d.finalMap) x)) ∧
    ∀ (v : HilbertSamuel.ResolutionWord) (T : TopologicalSpace.Closeds L.X),
      IsGreatest (Set.range (ν L)) v → (T : Set L.X) = {x | ν L x = v} →
      ((Scheme.IdealSheafData.vanishingIdeal T).comap d.finalMap).comap c.finalMap =
        (Scheme.IdealSheafData.vanishingIdeal T).comap e.finalMap ∧
      ((L.wordAmbientIdeal (Fin.last n) T).comap d.wordFinalAmbientMap).comap
          c.wordFinalAmbientMap =
        (L.wordAmbientIdeal (Fin.last n) T).comap e.wordFinalAmbientMap

/-- An intrinsic identification commutes with further smooth pullback over a commuting
square of initial intrinsic maps. This includes restricting both histories to open subsets.
Source: ILO VIII 2.3.13; BMT 6.1 Addendum (3), 6.3
(blueprint: lem-trf-resolution-word-finite-history-comparison). -/
def WordIntrinsicSmoothCoherence (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord) : Prop :=
  ∀ {A A' B B' : EmbeddedResolutionPair.{u}} {m n : ℕ}
    {H : EmbeddedResolutionHistory A m} {H' : EmbeddedResolutionHistory A' m}
    {K : EmbeddedResolutionHistory B n} {K' : EmbeddedResolutionHistory B' n}
    {a : A.X ≅ A'.X} {b : B.X ≅ B'.X}
    (f : EmbeddedResolutionSmoothMap A B) (g : EmbeddedResolutionSmoothMap A' B')
    (c : SmoothPullback f H K) (d : SmoothPullback g H' K')
    (i : IntrinsicComparison a H H') (j : IntrinsicComparison b K K'),
    Admissible ν K → Admissible ν K' →
    a.hom ≫ g.intrinsic = f.intrinsic ≫ b.hom →
    (i.iso.app (op (Fin.last m))).hom ≫ d.finalMap =
      c.finalMap ≫ (j.iso.app (op (Fin.last n))).hom ∧
    ∀ (v : HilbertSamuel.ResolutionWord) (T : TopologicalSpace.Closeds K'.X),
      IsGreatest (Set.range (ν K')) v → (T : Set K'.X) = {x | ν K' x = v} →
      ((Scheme.IdealSheafData.vanishingIdeal T).comap d.finalMap).comap
          (i.iso.app (op (Fin.last m))).hom =
        ((Scheme.IdealSheafData.vanishingIdeal T).comap
          (j.iso.app (op (Fin.last n))).hom).comap c.finalMap

/-- Smooth pullbacks of finite normalized-word histories exist after precisely empty-center
stages are deleted. The geometry, stagewise local formulas, all maximum-stratum ideals,
intrinsic comparison and repeated-pullback compatibility hold for the fixed prescription.

Source: ILO VIII 2.3.5(i), 2.3.11--2.3.13, pp. 92--94; BMT sections 6.1--6.3
(blueprint: lem-trf-resolution-word-finite-history-comparison).

Proof:
1. Induct on the generators of Admissible. Empty histories have the geometry of their
initial pair. For maximum extensions use lem-trf-resolution-word-maximum-center-descent,
lem-dl-a1-locally-closed-stratum-separated-finite-type and
lem-trf-regular-perfect-field-smooth to obtain a smooth closed center. Then apply
lem-trf-smooth-center-blowup-geometry. No terminating resolution is assumed.
2. Smooth maps are flat by lem-pc-smooth-flat. Use def-nagata-blowup-flat-base-change-map
and thm-nagata-blowup-flat-base-change at each ambient stage. Flat going down
(lem-sc-flat-going-down) gives the generic-component hypothesis of
lem-trf-strict-transform-flat-etale-base-change. The stage maps are smooth by
lem-pc-proper-base-change and composition by lem-trf-smooth-composition. The initial
pullback is reduced by lem-weil-pbc-finite-type-over-noetherian,
sbc-lem-smooth-geometrically-reduced and lem-sfb-flat-geometrically-reduced-pullback.
Apply smooth-center geometry inductively. By thm-nagata-global-blowup-complement a unit
center gives an identity ambient blowup: omit precisely those centers.
3. Apply lem-trf-hilbert-samuel-smooth-dimension-profile pointwise. The local fibre-ring
dimension s shifts q by s, preserves c and sums h s times. Cancellation of difference
with summation identifies normalized heads, without a constant-relative-dimension choice.
4. Use lem-trf-hilbert-samuel-local-presentations in minimal envelopes, retaining all
ordered earlier center ideals. The fixed lem-trf-marked-ideal-numerical-resolution-engine
identifies the numerical words under smooth pullback and test equivalence. Delete their
common leading one. lem-trf-normalized-resolution-word-gluing gives the global words.
A deleted unit center creates no exceptional divisor; original chronological positions
still identify the births of every retained exceptional component.
5. For intrinsic comparisons the identified stalk rings have the same maximal-ideal
powers, lengths and component dimensions. Local presentations and engine test equivalence
identify tails in equal-dimensional minimal envelopes, preserving ordered earlier ideals.
The gluing theorem identifies the prescribed words, without comparing ambient schemes.
6. A full maximum locus is closed by gluing. Give it its reduced structure using
lem-weil-pbc-reduced-induced-closed-subscheme. It is finite type, hence locally Noetherian.
Its smooth pullback is reduced by the geometrically reduced and flat pullback results.
Apply lem-trf-reduced-flat-pullback-recognition intrinsically and ambiently. Uniqueness
identifies the reduced ideals, even when the inverse-image stratum is not maximal.
An empty inverse image has unit ideal. The same uniqueness applies to intrinsic isomorphisms.
7. Values are compared in one fixed word space, so restriction and repeated pullback
compose their equalities. Ideal extension composes on local generators. A unit ideal
remains unit; a newly empty center is deleted at the next pullback. Thus the deletion maps
compose, preserving order and birth stages. The cartesian squares identify the actual
comparison maps. This includes open immersions, empty schemes and length-zero histories.
-/
theorem resolution_word_finite_history_comparison
    (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : ∀ {B : EmbeddedResolutionPair.{u}} {k : ℕ}
      (G : EmbeddedResolutionHistory B k), Admissible ν G →
      (∀ x : G.X, ¬ IsRegularLocalRing (G.X.presheaf.stalk x) →
        Nonempty (ResolutionWordChart R G x)) ∧
      (∀ (x : G.X) (C : ResolutionWordChart R G x),
        (R.value C.history ⟨C.supportPoint, C.cosupport⟩).head? =
          some (MarkedIdeal.rational 1) ∧ ν G x = C.word) ∧
      (Set.range (ν G)).Finite ∧
      (∀ v : HilbertSamuel.ResolutionWord, IsClosed {x : G.X | v ≤ ν G x}) ∧
      (∀ x : G.X, ν G x = ⊥ ↔ IsRegularLocalRing (G.X.presheaf.stalk x)) ∧
      ∀ (D : ℕ) (_hD : topologicalKrullDim G.X ≤ (D : WithBot ℕ∞)) (x y : G.X),
        (HilbertSamuel.sumResolutionWord D (ν G x) ≤
            HilbertSamuel.sumResolutionWord D (ν G y) ↔ ν G x ≤ ν G y) ∧
        (HilbertSamuel.sumResolutionWord D (ν G x) =
            HilbertSamuel.sumResolutionWord D (ν G y) ↔ ν G x = ν G y)) :
    (∀ {B : EmbeddedResolutionPair.{u}} {n : ℕ} (K : EmbeddedResolutionHistory B n),
      Admissible ν K → WordHistoryGeometry K) ∧
    (∀ (B : EmbeddedResolutionPair.{u}) (Q : Scheme.{u}) (g : Q ⟶ B.P),
      Smooth g → IsSeparated (g ≫ B.base) → LocallyOfFiniteType (g ≫ B.base) →
      QuasiCompact (g ≫ B.base) → IsReduced (pullback B.inclusion g)) ∧
    (∀ {A B : EmbeddedResolutionPair.{u}} {n : ℕ}
      (f : EmbeddedResolutionSmoothMap A B) (K : EmbeddedResolutionHistory B n),
      Admissible ν K → ∃ (m : ℕ) (H : EmbeddedResolutionHistory A m),
        Nonempty (SmoothPullback f H K)) ∧
    (∀ {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
      {f : EmbeddedResolutionSmoothMap A B}
      {H : EmbeddedResolutionHistory A m} {K : EmbeddedResolutionHistory B n}
      (c : SmoothPullback f H K), Admissible ν K → WordSmoothComparison R ν c) ∧
    (∀ {A B : EmbeddedResolutionPair.{u}} {n : ℕ} {e : A.X ≅ B.X}
      {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory B n}
      (c : IntrinsicComparison e H K),
      Admissible ν H → Admissible ν K → WordIntrinsicComparison ν c) ∧
    WordPullbackCoherence ν ∧ WordIntrinsicSmoothCoherence ν := by
  sorry

end AlgebraicGeometry.EmbeddedResolutionHistory
