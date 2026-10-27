/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.ResolutionInvariantCalculusData
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

/-! # Finite chronological maximum histories

Source: ILO VIII 2.3.1, 2.3.11--2.3.13, pp. 91--94; the conditional recursion
in Steps 1, 2 and 4 of (blueprint: lem-trf-maximum-history-chronology).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open EmbeddedResolutionHistory

/-- A finite chronological run before choosing invariant labels or lower cuts.
Source: ILO VIII 2.3.1, 2.3.11 (blueprint: lem-trf-maximum-history-chronology). -/
structure MaximumHistorySegment {V : Type w} [LinearOrder V] [OrderBot V]
    (ν : ResolutionInvariantCalculus.{u} V) (A : EmbeddedResolutionPair.{u}) (r : ℕ) where
  history : ∀ i : Fin (r + 1), EmbeddedResolutionHistory A i.val
  extension : ∀ i : Fin r, Extension (history i.castSucc) (history i.succ)
  admissible : ∀ i, Admissible ν.value (history i)
  nonregular : ∀ i : Fin r, ¬ IsRegularScheme (history i.castSucc).X
  maximum : ∀ i, IsMaximumStep ν.value (extension i)

private def emptyHistory (A : EmbeddedResolutionPair.{u}) : EmbeddedResolutionHistory A 0 where
  ambient := (Functor.const _).obj A.P
  intrinsic := (Functor.const _).obj A.X
  inclusion := { app := fun _ ↦ A.inclusion }
  closed := fun _ ↦ A.closed
  initialAmbient := Iso.refl _
  initialIntrinsic := Iso.refl _
  initialInclusion := by simp
  center := fun j ↦ Fin.elim0 j
  centerToIntrinsic := fun j ↦ Fin.elim0 j
  centerClosed := fun j ↦ Fin.elim0 j
  centerInclusion := fun j ↦ Fin.elim0 j
  ambientBlowup := fun j ↦ Fin.elim0 j
  ambientBlowupMap := fun j ↦ Fin.elim0 j
  strictTransform := fun j ↦ Fin.elim0 j
  strictTransformMap := fun j ↦ Fin.elim0 j
  strictTransformToSource := fun j ↦ Fin.elim0 j

private def emptySegment {V : Type w} [LinearOrder V] [OrderBot V]
    (ν : ResolutionInvariantCalculus.{u} V) (A : EmbeddedResolutionPair.{u}) :
    MaximumHistorySegment ν A 0 where
  history := Fin.cases (emptyHistory A) (fun j ↦ Fin.elim0 j)
  extension := fun j ↦ Fin.elim0 j
  admissible := Fin.cases (.empty _) (fun j ↦ Fin.elim0 j)
  nonregular := fun j ↦ Fin.elim0 j
  maximum := fun j ↦ Fin.elim0 j

private def transportMaximumStep {V : Type w} [LinearOrder V] [OrderBot V]
    {ν : ResolutionInvariantCalculus.{u} V} {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H H' : EmbeddedResolutionHistory A n} {K K' : EmbeddedResolutionHistory A (n + 1)}
    (h : H = H') (k : K = K')
    (E : {E : Extension H K // IsMaximumStep ν.value E}) :
    {E : Extension H' K' // IsMaximumStep ν.value E} := by
  subst H'
  subst K'
  exact E

private def appendSegment {V : Type w} [LinearOrder V] [OrderBot V]
    {ν : ResolutionInvariantCalculus.{u} V} {A : EmbeddedResolutionPair.{u}} {r : ℕ}
    (S : MaximumHistorySegment ν A r) (K : EmbeddedResolutionHistory A (r + 1))
    (E : Extension (S.history (Fin.last r)) K)
    (h : ¬ IsRegularScheme (S.history (Fin.last r)).X)
    (hm : IsMaximumStep ν.value E) : MaximumHistorySegment ν A (r + 1) := by
  let H : ∀ i : Fin (r + 2), EmbeddedResolutionHistory A i.val := Fin.snoc S.history K
  have hc (i : Fin (r + 1)) : H i.castSucc = S.history i := Fin.snoc_castSucc _ _ _
  have hl : H (Fin.last (r + 1)) = K := Fin.snoc_last _ _
  let he : ∀ i : Fin (r + 1),
      {E : Extension (H i.castSucc) (H i.succ) // IsMaximumStep ν.value E} :=
    Fin.lastCases
      (transportMaximumStep (hc (Fin.last r)).symm hl.symm ⟨E, hm⟩)
      (fun i ↦ transportMaximumStep (hc i.castSucc).symm (hc i.succ).symm
        ⟨S.extension i, S.maximum i⟩)
  refine ⟨H, fun i ↦ (he i).val, ?_, ?_, fun i ↦ (he i).property⟩
  · refine Fin.lastCases ?_ (fun i ↦ ?_)
    · simpa only [hl] using Admissible.step E (S.admissible (Fin.last r)) hm
    · simpa only [hc] using S.admissible i
  · refine Fin.lastCases ?_ (fun i ↦ ?_)
    · simpa only [hc] using h
    · simpa only [hc] using S.nonregular i

/-- A terminating calculus admits a finite chronological maximum run ending at regularity.
Source: ILO VIII 2.3.1 and 2.3.11, pp. 91, 93
(blueprint: lem-trf-maximum-history-chronology).

Proof: start with the constant length-zero diagram. Append a maximum extension whenever
the current last transform is nonregular. Admissibility is preserved by its step rule.
If no finite run ended regularly, choose an extension of every finite run. Natural-number
recursion then constructs one run of each length, each extending its predecessor. Their
last histories and last extensions form the infinite maximum chain forbidden by the
termination clause. Thus a regular endpoint exists. No order-theoretic termination
hypothesis on the value set is used. -/
private theorem maximumHistorySegment_exists {V : Type w} [LinearOrder V] [OrderBot V]
    (ν : ResolutionInvariantCalculus.{u} V) (A : EmbeddedResolutionPair.{u}) :
    ∃ r, ∃ S : MaximumHistorySegment ν A r,
      IsRegularScheme (S.history (Fin.last r)).X := by
  classical
  by_contra hn
  have nonregular (r : ℕ) (S : MaximumHistorySegment ν A r) :
      ¬ IsRegularScheme (S.history (Fin.last r)).X := fun h ↦ hn ⟨r, S, h⟩
  have next (r : ℕ) (S : MaximumHistorySegment ν A r) :
      ∃ K : EmbeddedResolutionHistory A (r + 1),
        ∃ E : Extension (S.history (Fin.last r)) K, IsMaximumStep ν.value E :=
    ν.maximumExists _ (S.admissible _) (nonregular r S)
  let K (r : ℕ) (S : MaximumHistorySegment ν A r) := (next r S).choose
  let E (r : ℕ) (S : MaximumHistorySegment ν A r) := (next r S).choose_spec.choose
  have hm (r : ℕ) (S : MaximumHistorySegment ν A r) :
      IsMaximumStep ν.value (E r S) := (next r S).choose_spec.choose_spec
  let S : (r : ℕ) → MaximumHistorySegment ν A r := fun r ↦ Nat.rec
    (emptySegment ν A) (fun r S ↦ appendSegment S (K r S) (E r S)
      (nonregular r S) (hm r S)) r
  have last (r : ℕ) : (S (r + 1)).history (Fin.last (r + 1)) = K r (S r) :=
    by simp only [S, appendSegment, Fin.snoc_last]
  apply ν.termination A
  refine ⟨fun r ↦ (S r).history (Fin.last r), ?_⟩
  let ext (r : ℕ) : {E : Extension ((S r).history (Fin.last r))
      ((S (r + 1)).history (Fin.last (r + 1))) // IsMaximumStep ν.value E} :=
    transportMaximumStep rfl (last r).symm ⟨E r (S r), hm r (S r)⟩
  exact ⟨fun r ↦ (ext r).val, fun r ↦ (ext r).property⟩

/-- A stopped chronological history with its positive reverse-order maxima and geometry,
before extension to all lower cuts. Source: ILO VIII 2.3.1, 2.3.5(ii), 2.3.11--2.3.13
(blueprint: lem-trf-maximum-history-chronology). -/
structure MaximumHistoryChronology {V : Type w} [LinearOrder V] [OrderBot V]
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

private theorem regular_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : IsRegularScheme Y) : IsRegularScheme X := by
  have : IsLocallyNoetherian Y := h.1
  have : IsRegular Y := h.2
  exact ⟨isLocallyNoetherian_of_isOpenImmersion e.hom,
    ⟨isRegularLocalRing_stalk_of_etale e.hom (fun _ ↦ inferInstance)⟩⟩

private theorem initialGeometry {A : EmbeddedResolutionPair.{u}}
    (H : EmbeddedResolutionHistory A 0) :
    Smooth H.base ∧ IsSeparated H.base ∧ LocallyOfFiniteType H.base ∧
      QuasiCompact H.base ∧ IsReduced H.X := by
  have : Smooth A.base := A.smooth
  have : IsSeparated A.base := A.separated
  have : LocallyOfFiniteType A.base := A.finiteType
  have : QuasiCompact A.base := A.quasiCompact
  have : IsReduced A.X := A.reduced
  have hb : H.base = H.initialAmbient.hom ≫ A.base := by
    change H.ambient.map (𝟙 (op (0 : Fin 1))) ≫ H.initialAmbient.hom ≫ A.base = _
    rw [H.ambient.map_id, Category.id_comp]
  rw [hb]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    isReduced_of_isOpenImmersion H.initialIntrinsic.hom⟩

/-- A terminating calculus has a stopped chronological history with strictly increasing
reverse-order positive maxima and all center and intermediate geometry.
Source: ILO VIII 2.3.1, 2.3.5(ii), 2.3.11--2.3.13, pp. 91--94
(blueprint: lem-trf-maximum-history-chronology).

Proof: the finite-run argument above gives a regular endpoint and nonregular earlier
stages. Choose the greatest value supplied by each maximum step; positivity removes the
bottom value. Strict progress applied to consecutive extensions says that these greatest
values strictly decrease, so their order-dual labels strictly increase. The calculus gives
center geometry at every extension and intermediate geometry after it; the initial stage
has the geometry of the input pair by its recorded initial isomorphisms. If the input is
regular, its initial history is regular, so no first extension can occur. An empty input
is regular: it is locally Noetherian by its finite-type closed embedding in the rational
ambient scheme, and the condition on stalks is vacuous. -/
theorem maximumHistoryChronology_exists {V : Type w} [LinearOrder V] [OrderBot V]
    (ν : ResolutionInvariantCalculus.{u} V) (A : EmbeddedResolutionPair.{u}) :
    ∃ r, Nonempty (MaximumHistoryChronology ν A r) := by
  classical
  obtain ⟨r, S, hreg⟩ := maximumHistorySegment_exists ν A
  let m (i : Fin r) : V := (S.maximum i).choose
  have hg (i : Fin r) : IsGreatest (Set.range (ν.value (S.history i.castSucc))) (m i) :=
    (S.maximum i).choose_spec.1
  have hp (i : Fin r) : ⊥ < m i := (S.maximum i).choose_spec.2.1
  let label : Fin r → OrderDual {v : V // v ≠ ⊥} := fun i ↦ ⟨m i, (hp i).ne'⟩
  have increasing : StrictMono label := by
    cases r with
    | zero => exact fun i ↦ Fin.elim0 i
    | succ n =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      change m i.succ < m i.castSucc
      apply ν.strictProgress (S.extension i.castSucc) (S.admissible _) (S.maximum _)
      · exact hg i.castSucc
      · simpa only [Fin.succ_castSucc] using hg i.succ
      · exact hp i.succ
  have regularInput : IsRegularScheme A.X → r = 0 := by
    intro h
    by_contra hr
    have nr := S.nonregular ⟨0, Nat.pos_of_ne_zero hr⟩
    exact nr (regular_of_iso (S.history 0).initialIntrinsic h)
  have emptyInput : IsEmpty A.X → r = 0 := by
    intro he
    have : IsEmpty A.X := he
    have : LocallyOfFiniteType A.base := A.finiteType
    have : IsClosedImmersion A.inclusion := A.closed
    have : IsLocallyNoetherian A.P := LocallyOfFiniteType.isLocallyNoetherian A.base
    have : IsLocallyNoetherian A.X := LocallyOfFiniteType.isLocallyNoetherian A.inclusion
    exact regularInput ⟨inferInstance, ⟨fun x ↦ isEmptyElim x⟩⟩
  refine ⟨r, ⟨{
    history := S.history
    extension := S.extension
    admissible := S.admissible
    nonregular := S.nonregular
    maximum := S.maximum
    label := label
    positive := hp
    greatest := hg
    increasing := increasing
    centerGeometry := fun i ↦ ν.maximumGeometry (S.extension i) (S.admissible _)
      (S.maximum i)
    intermediateGeometry := ?_
    finalRegular := hreg
    regularInput := regularInput
    emptyInput := emptyInput }⟩⟩
  intro i
  induction i using Fin.cases with
  | zero => exact initialGeometry (S.history 0)
  | succ i => exact ν.nextGeometry (S.extension i) (S.admissible _) (S.maximum i)

end AlgebraicGeometry
