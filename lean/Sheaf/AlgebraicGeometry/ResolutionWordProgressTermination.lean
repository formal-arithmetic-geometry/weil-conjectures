module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing
public import Sheaf.AlgebraicGeometry.ResolutionWordMaximumCenterDescent
public import Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile
public import Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Progress and termination of the normalized resolution word

Source: ILO VIII, Remark 2.3.11, p. 93, singular-locus phase before exceptional cleanup;
BMT Theorem 6.1 and Addendum (2), sections 6.1--6.3
(blueprint: lem-trf-resolution-word-progress-termination).

The input word is the fixed assignment of the gluing lemma. All process relations below
use the existing ordinary blowups, schematic strict transforms and ordered center histories.
Finite constant-head intervals retain their actual controlled local presentations. No
well-foundedness assertion is made about the entire ordered alphabet.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- The property of the fixed assignment supplied by `normalized_resolution_word_gluing`.
This just names that theorem's entire output, without choosing a different invariant.
Source: ILO VIII 2.3.11--2.3.13; node statement's fixed-word hypothesis
(blueprint: lem-trf-resolution-word-progress-termination). -/
def IsNormalizedResolutionWord (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord) : Prop :=
  ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n),
    Admissible ν H →
    (∀ x : H.X, ¬ IsRegularLocalRing (H.X.presheaf.stalk x) →
      Nonempty (ResolutionWordChart R H x)) ∧
    (∀ (x : H.X) (C : ResolutionWordChart R H x),
      (R.value C.history ⟨C.supportPoint, C.cosupport⟩).head? =
        some (MarkedIdeal.rational 1) ∧ ν H x = C.word) ∧
    (Set.range (ν H)).Finite ∧
    (∀ v : HilbertSamuel.ResolutionWord, IsClosed {x : H.X | v ≤ ν H x}) ∧
    (∀ x : H.X, ν H x = ⊥ ↔ IsRegularLocalRing (H.X.presheaf.stalk x)) ∧
    ∀ (D : ℕ) (_hD : topologicalKrullDim H.X ≤ (D : WithBot ℕ∞)) (x y : H.X),
      (HilbertSamuel.sumResolutionWord D (ν H x) ≤
          HilbertSamuel.sumResolutionWord D (ν H y) ↔ ν H x ≤ ν H y) ∧
      (HilbertSamuel.sumResolutionWord D (ν H x) =
          HilbertSamuel.sumResolutionWord D (ν H y) ↔ ν H x = ν H y)

/-- The geometric induction condition on a raw stage; it is a conclusion of progress,
not part of the raw history's data.
Source: ILO VIII 2.3.11; node statement's geometric hypotheses and preservation clause
(blueprint: lem-trf-resolution-word-progress-termination). -/
def HasResolutionGeometry {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) : Prop :=
  Smooth H.base ∧ IsSeparated H.base ∧ LocallyOfFiniteType H.base ∧
    QuasiCompact H.base ∧ IsReduced H.X

/-- Histories obtained from an empty history by this process alone. The raw diagrams
and every ordered old center ideal are retained by the existing `Extension`.
Source: ILO VIII 2.3.1 and 2.3.11; node statement's maximum-center process
(blueprint: lem-trf-resolution-word-progress-termination). -/
inductive MaximumHistory (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord) :
    ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}, EmbeddedResolutionHistory A n → Prop
  | empty {A : EmbeddedResolutionPair.{u}} (H : EmbeddedResolutionHistory A 0) :
      MaximumHistory ν H
  | step {A : EmbeddedResolutionPair.{u}} {n : ℕ}
      {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
      (E : Extension H K) : MaximumHistory ν H → IsMaximumStep ν E → MaximumHistory ν K

/-- The next intrinsic structure map, transported to the preceding history by its
extension isomorphism; it is the canonical strict-transform projection.
Source: ILO VIII 2.3.1 and 2.3.11; node proof step 1
(blueprint: lem-trf-resolution-word-progress-termination). -/
def Extension.resolutionMap {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (E : Extension H K) : K.X ⟶ H.X :=
  K.intrinsic.map (homOfLE (Fin.last n).castSucc_le_succ).op ≫
    (E.intrinsic (Fin.last n)).inv

/-- Exact synchronization on a finite constant-head interval. Each local history starts
with a genuine word chart, keeps its initial history and boundary births, and evolves by
controlled transforms. Its cosupport is exactly the retained-head locus, and its reduced
center ideal is the pullback of the actual global center ideal. The maximum is taken over
the union of the local tails; a patch missing it has empty center. Different initial chart
history lengths are allowed, so earlier centers are never discarded to align indices.
Source: ILO VIII 2.3.11 and 2.3.5(ii); node proof steps 2 and 4
(blueprint: lem-trf-resolution-word-progress-termination). -/
structure HeadIntervalPresentations (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    {A : EmbeddedResolutionPair.{u}} {n l : ℕ}
    (H : ∀ j : Fin (l + 1), EmbeddedResolutionHistory A (n + j.val))
    (E : ∀ j : Fin l, Extension (H j.castSucc) (H j.succ))
    (a : HilbertSamuel.DimensionHead) where
  patches : ℕ
  point : Fin patches → (H 0).X
  pointHead : ∀ i, HilbertSamuel.normalizedHead (H 0).X (point i) = a
  chart : ∀ i, ResolutionWordChart R (H 0) (point i)
  length : Fin patches → ℕ
  chartLength : ∀ i, (chart i).length = length i
  localHistory : ∀ (i : Fin patches) (j : Fin (l + 1)),
    MarkedIdeal.History (length i + j.val)
  initial : ∀ i, HEq (localHistory i 0) (chart i).history
  extension : ∀ (i : Fin patches) (j : Fin l),
    MarkedIdeal.Extension (localHistory i j.castSucc) (localHistory i j.succ)
  admissible : ∀ (i : Fin patches) (j : Fin (l + 1)),
    MarkedIdeal.Admissible R.value (localHistory i j)
  maximalOrder : ∀ (i : Fin patches) (j : Fin (l + 1)), (localHistory i j).last.IsMaximalOrder
  intrinsic : ∀ (i : Fin patches) (j : Fin (l + 1)), (localHistory i j).last.ambient.X ⟶ (H j).X
  etale : ∀ (i : Fin patches) (j : Fin (l + 1)), Etale (intrinsic i j)
  initialMap : ∀ i, HEq (intrinsic i 0) (chart i).finalMap
  transition : ∀ (i : Fin patches) (j : Fin l),
    (localHistory i j.succ).last.ambient.X ⟶ (localHistory i j.castSucc).last.ambient.X
  transitionSquare : ∀ (i : Fin patches) (j : Fin l),
    transition i j ≫ (localHistory i j.castSucc).last.ambient.i =
      (localHistory i j.succ).last.ambient.i ≫
        ((localHistory i j.succ).step (Fin.last (length i + j.val))).step.π ≫
          eqToHom (congrArg (fun B : MarkedIdeal.{u} ↦ B.ambient.Z)
            ((extension i j).states (Fin.last (length i + j.val))).symm)
  cartesian : ∀ (i : Fin patches) (j : Fin l), IsPullback (transition i j) (intrinsic i j.succ)
    (intrinsic i j.castSucc) (E j).resolutionMap
  cosupportPoint : ∀ (i : Fin patches) (j : Fin (l + 1)),
    (localHistory i j).last.cosupport → (localHistory i j).last.ambient.X
  cosupportSquare : ∀ (i : Fin patches) (j : Fin (l + 1)) x,
    (localHistory i j).last.ambient.i (cosupportPoint i j x) =
      (localHistory i j).last.marked.j x.val
  retained : ∀ (i : Fin patches) (j : Fin (l + 1)), Set.range (cosupportPoint i j) =
    {x | HilbertSamuel.normalizedHead (H j).X ((intrinsic i j) x) = a}
  cover : ∀ j (x : (H j).X), HilbertSamuel.normalizedHead (H j).X x = a →
    ∃ (i : Fin patches) (y : (localHistory i j).last.ambient.X), (intrinsic i j) y = x
  word : ∀ (i : Fin patches) (j : Fin (l + 1)) x, ν (H j) ((intrinsic i j) (cosupportPoint i j x)) =
    some (toLex (a, (R.value (localHistory i j) x).drop 1))
  leadingOne : ∀ (i : Fin patches) (j : Fin (l + 1)) x,
    (R.value (localHistory i j) x).head? = some (MarkedIdeal.rational 1)
  centers : ∀ (i : Fin patches) (j : Fin l),
    ∃ c : ((localHistory i j.succ).step
        (Fin.last (length i + j.val))).step.center.subscheme ⟶
          (localHistory i j.castSucc).last.ambient.X,
      IsClosedImmersion c ∧
      c ≫ (localHistory i j.castSucc).last.ambient.i =
        (extension i j).centerMap ≫ (localHistory i j.castSucc).last.marked.j ∧
      c.ker = (E j).centerMap.ker.comap (intrinsic i j.castSucc)
  synchronized : ∀ j : Fin l, ∃ t : MarkedIdeal.Word,
    (∃ (i : Fin patches) (x : (localHistory i j.castSucc).last.cosupport),
      (R.value (localHistory i j.castSucc) x).drop 1 = t) ∧
    (∀ (i : Fin patches) (x : (localHistory i j.castSucc).last.cosupport),
      (R.value (localHistory i j.castSucc) x).drop 1 ≤ t) ∧
    ∀ i : Fin patches, Set.range (extension i j).centerMap =
      {x | ∃ hx : x ∈ (localHistory i j.castSucc).last.cosupport,
        (R.value (localHistory i j.castSucc) ⟨x, hx⟩).drop 1 = t}

/-- The full reduced maximum stratum gives a permissible extension, preserving ambient
smoothness, separatedness, finite type and reducedness of the strict transform. Every such
maximum extension has the same geometric preservation and strict word progress.
Source: ILO VIII 2.3.11; node proof steps 1--3
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: The gluing lemma gives an attained positive maximum. Maximum-center descent
identifies its reduced closed subscheme with the smooth local presentation centers, with
adapted normal crossings. A closed subscheme of a finite-type rational scheme is finite type;
regularity of the center implies smoothness over the perfect field Q. Apply
lem-trf-smooth-center-blowup-geometry, transport along the recorded isomorphisms and append
this ideal to the whole old diagram. On the retained head the presenting word is (1,t), so
removing the common leading one identifies its maximum center with the full word maximum.
The marked-ideal engine strictly lowers the greatest tail, or empties cosupport and removes
the head. All lower heads remain lower by the dimension-profile nonincrease theorem.
Finite image then gives strict inequality of the attained next maximum. -/
theorem resolution_word_progress (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν)
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n)
    (hH : Admissible ν H) (hgeom : HasResolutionGeometry H) :
    (¬ IsRegularScheme H.X →
      ∃ (K : EmbeddedResolutionHistory A (n + 1)) (E : Extension H K), IsMaximumStep ν E) ∧
    (∀ (K : EmbeddedResolutionHistory A (n + 1)) (E : Extension H K),
      IsMaximumStep ν E → HasResolutionGeometry K ∧
        ∀ (m m' : HilbertSamuel.ResolutionWord),
          IsGreatest (Set.range (ν H)) m → IsGreatest (Set.range (ν K)) m' →
          ¬ IsRegularScheme K.X → m' < m) := by
  sorry

/-- The next global center is a permissible maximum center on local presentations,
with equality of the actual pulled-back ideals and the required boundary condition.
Source: ILO VIII 2.3.11; node proof steps 1--2
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: Apply maximum-center descent at each point of the full maximum stratum. Its
smooth marked centers are identified scheme-theoretically with the pullback of the reduced
full stratum, not only with its points. The actual extension center is reduced with that
same support, so uniqueness of the reduced induced structure identifies its ideal with this
one. The marked engine provides the controlled next history and adapted normal crossings.
Thus the identification holds even if this step removes the old head completely. -/
theorem resolution_word_permissible (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν)
    {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (hH : Admissible ν H) (hgeom : HasResolutionGeometry H)
    (E : Extension H K) (hE : IsMaximumStep ν E) :
    ∀ x ∈ Set.range E.centerMap, ∃ C : ResolutionWordChart R H x,
      Etale C.finalMap ∧
      ∃ (L : MarkedIdeal.History (C.length + 1))
        (F : MarkedIdeal.Extension C.history L),
        MarkedIdeal.IsMaximumStep R.value F ∧
        IsReduced (L.step (Fin.last C.length)).step.center.subscheme ∧
        HasAdaptedNormalCrossingsCenter (F.centerMap ≫ C.history.last.marked.j).ker
          (fun i ↦ C.history.last.ambient.boundary.get i) ∧
        ∃ c : (L.step (Fin.last C.length)).step.center.subscheme ⟶ C.history.last.ambient.X,
          IsClosedImmersion c ∧
          c ≫ C.history.last.ambient.i = F.centerMap ≫ C.history.last.marked.j ∧
          c.ker = E.centerMap.ker.comap C.finalMap := by
  classical
  obtain ⟨mE, hmE, hposE, hredE, hrange⟩ := hE
  have hNR : ¬ IsRegularScheme H.X := by
    intro hr
    have : IsRegular H.X := hr.2
    obtain ⟨y, hy⟩ := hmE.1
    have hb := ((hν H hH).2.2.2.2.1 y).mpr (IsRegular.isRegularLocalRing_stalk y)
    exact (ne_of_gt hposE) (hy.symm.trans hb)
  obtain ⟨m, T, hm, _, hT, _, _, _, _, _, _, _, hlocal⟩ :=
    resolution_word_maximum_center_descent R ν hν H hH
      ⟨hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1⟩ hgeom.2.2.2.2 hNR
  have hsame : mE = m := hmE.unique hm
  have hrangeT : Set.range E.centerMap = (T : Set H.X) := by
    rw [hrange, hsame, hT]
  have : IsReduced (K.center (Fin.last n)).subscheme := hredE
  have hker : E.centerMap.ker = Scheme.IdealSheafData.vanishingIdeal T := by
    rw [E.centerMap.ker_eq_vanishingIdeal]
    congr 1
    apply TopologicalSpace.Closeds.ext
    change closure (Set.range E.centerMap) = (T : Set H.X)
    rw [hrangeT, T.isClosed.closure_eq]
  intro x hx
  rw [hrangeT] at hx
  obtain ⟨C, het, L, F, hF, hredL, _, hnc, c, hc, hfac, hkerC, _⟩ := hlocal x hx
  refine ⟨C, het, L, F, hF, hredL, hnc, c, hc, hfac, ?_⟩
  rw [hker]
  exact hkerC

/-- Heads do not increase under a maximum extension, both pointwise and at an attained
maximum. Adjoining bottom lets the latter assertion include an empty next scheme.
Source: ILO VIII 2.3.11; node proof step 2
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: The maximum-center descent theorem gives a smooth center on a constant normalized
head with the recorded earlier ideals. Apply the dimension-profile admissible-blowup
nonincrease theorem, cancelling the common summation used there to compare raw heads.
Transport along the actual strict-transform isomorphism. Every new head lies below its
old image head; taking greatest values proves the second clause, including bottom. -/
theorem resolution_word_head_nonincrease (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν)
    {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (hH : Admissible ν H) (hgeom : HasResolutionGeometry H)
    (E : Extension H K) (hE : IsMaximumStep ν E) :
    (∀ x : K.X, HilbertSamuel.normalizedHead K.X x ≤
      HilbertSamuel.normalizedHead H.X (E.resolutionMap x)) ∧
    ∀ a b : WithBot HilbertSamuel.DimensionHead,
      IsGreatest (insert ⊥
        ((fun h : HilbertSamuel.DimensionHead ↦ (h : WithBot HilbertSamuel.DimensionHead)) ''
        Set.range (HilbertSamuel.normalizedHead H.X))) a →
      IsGreatest (insert ⊥
        ((fun h : HilbertSamuel.DimensionHead ↦ (h : WithBot HilbertSamuel.DimensionHead)) ''
        Set.range (HilbertSamuel.normalizedHead K.X))) b →
      b ≤ a := by
  sorry

/-- No infinite strictly decreasing chain of attained greatest heads can arise from one
fixed initial input, even when consecutive chosen heads are separated by finite plateaus.
Source: ILO VIII 2.3.11; node proof step 5
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: Progress preserves the geometric hypotheses at every finite prefix. These are
admissible blowups of the fixed initial finite-dimensional scheme. Apply the reachable-head
descending-chain clause of lem-trf-hilbert-samuel-smooth-dimension-profile in one common
dimension bound and cancel its common summation. Reachability allows arbitrary finite gaps,
so recording the values just after strict head changes is covered. Thus strict changes in
any one run can occur only finitely often. The ordered histories and finite disjoint unions
are included in that profile theorem. -/
theorem resolution_word_finitely_many_head_drops (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν) (A : EmbeddedResolutionPair.{u})
    (a : ℕ → HilbertSamuel.DimensionHead)
    (ha : ∀ k : ℕ, ∃ (n : ℕ) (H : EmbeddedResolutionHistory A n),
      MaximumHistory ν H ∧ IsGreatest (Set.range (HilbertSamuel.normalizedHead H.X)) (a k)) :
    ¬ ∀ k : ℕ, a (k + 1) < a k := by
  sorry

/-- On every finite constant-head interval the very same local presentations evolve by
synchronized maximum-center controlled transforms. Empty cosupport removes the head.
Source: ILO VIII 2.3.11 and 2.3.5(ii); node proof steps 2 and 4
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: Take a finite etale presentation cover of the closed greatest-head stratum at the
starting stage, with the earlier center ideals and births supplied by the gluing charts.
Induct on the interval length. The all-finite-test-sequences presentation clause identifies
the controlled cosupport with exactly the retained-head locus; the gluing clause identifies
the tails with the fixed engine values. Maximum-center descent identifies the actual reduced
center ideals, so their pullbacks give precisely the synchronized maximum over the family.
Patches missing the maximum have empty centers. Keep pulling back this fixed family, rather
than choosing a new resolution. Equality of cosupport and retained locus and the covering
clause show that emptying all final cosupports removes the head globally. -/
theorem resolution_word_constant_head_presentations (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν)
    {A : EmbeddedResolutionPair.{u}} {n l : ℕ}
    (H : ∀ j : Fin (l + 1), EmbeddedResolutionHistory A (n + j.val))
    (E : ∀ j : Fin l, Extension (H j.castSucc) (H j.succ))
    (hH : Admissible ν (H 0)) (hgeom : HasResolutionGeometry (H 0))
    (hE : ∀ j, IsMaximumStep ν (E j)) (a : HilbertSamuel.DimensionHead)
    (ha : HilbertSamuel.regularHead < a)
    (hhead : ∀ j, IsGreatest (Set.range (HilbertSamuel.normalizedHead (H j).X)) a) :
    Nonempty (HeadIntervalPresentations R ν H E a) := by
  sorry

/-- Emptying the continued presentations removes their retained head, including the case
of an empty final strict transform.
Source: ILO VIII 2.3.11; node proof steps 3--4
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: If a final point retained the head, the covering field supplies a local preimage.
The retained-locus equality then puts this preimage in the range of the local cosupport,
contradicting its emptiness. These equalities are the presentation theorem after the whole
finite sequence, not merely equality of initial loci. -/
theorem resolution_word_empty_cosupport_removes_head
    (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    {A : EmbeddedResolutionPair.{u}} {n l : ℕ}
    {H : ∀ j : Fin (l + 1), EmbeddedResolutionHistory A (n + j.val)}
    {E : ∀ j : Fin l, Extension (H j.castSucc) (H j.succ)}
    {a : HilbertSamuel.DimensionHead} (P : HeadIntervalPresentations R ν H E a)
    (hempty : ∀ i, (P.localHistory i (Fin.last l)).last.cosupport = ∅) :
    ∀ x : (H (Fin.last l)).X,
      HilbertSamuel.normalizedHead (H (Fin.last l)).X x ≠ a := by
  intro x hx
  obtain ⟨i, y, hy⟩ := P.cover (Fin.last l) x hx
  have hret : y ∈ Set.range (P.cosupportPoint i (Fin.last l)) := by
    rw [P.retained]
    change HilbertSamuel.normalizedHead (H (Fin.last l)).X
      ((P.intrinsic i (Fin.last l)) y) = a
    rw [hy]
    exact hx
  obtain ⟨z, _⟩ := hret
  exact (Set.eq_empty_iff_forall_notMem.mp (hempty i)) z.val z.property

/-- A constant greatest singular head cannot persist for an infinite tail beginning at
any finite stage; the presentations at that stage, with their earlier history, terminate.
Source: ILO VIII 2.3.11; node proof step 4
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: Fix the finite cover at the starting stage and continue it inductively, as in the
finite-interval theorem. This gives exactly the synchronized engine process, retaining
empty-center patches. Its finite-family termination theorem applies to the same controlled
histories and words. Empty cosupport removes the head by the local-presentation theorem,
contradicting its persistence as an attained greatest head. This argument is on finite
prefixes and does not presuppose a completed embedded resolution tower. -/
theorem resolution_word_no_constant_head_tail (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν)
    {A : EmbeddedResolutionPair.{u}} (n : ℕ)
    (H : ∀ k : ℕ, EmbeddedResolutionHistory A (n + k))
    (E : ∀ k : ℕ, Extension (H k) (H (k + 1)))
    (hH : Admissible ν (H 0)) (hgeom : HasResolutionGeometry (H 0))
    (hE : ∀ k, IsMaximumStep ν (E k)) (a : HilbertSamuel.DimensionHead)
    (ha : HilbertSamuel.regularHead < a) :
    ¬ ∀ k, IsGreatest (Set.range (HilbertSamuel.normalizedHead (H k).X)) a := by
  sorry

private theorem greatest_head_of_maximum_step
    (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν)
    {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (hH : Admissible ν H) (hgeom : HasResolutionGeometry H)
    (E : Extension H K) (hE : IsMaximumStep ν E) :
    ∃ a : HilbertSamuel.DimensionHead, HilbertSamuel.regularHead < a ∧
      IsGreatest (Set.range (HilbertSamuel.normalizedHead H.X)) a := by
  classical
  have : LocallyOfFiniteType H.base := hgeom.2.2.1
  have : QuasiCompact H.base := hgeom.2.2.2.1
  have : IsReduced H.X := hgeom.2.2.2.2
  have : IsClosedImmersion (H.inclusion.app (op (Fin.last n))) := H.closed _
  let p : H.X ⟶ Spec (.of (ULift.{u} ℚ)) :=
    H.inclusion.app (op (Fin.last n)) ≫ H.base
  obtain ⟨m, hm, hpos, -⟩ := hE
  obtain ⟨x, hx⟩ := hm.1
  have hxsing : ¬ IsRegularLocalRing (H.X.presheaf.stalk x) := by
    intro hr
    have hb := ((hν H hH).2.2.2.2.1 x).mpr hr
    exact (ne_of_gt hpos) (hx.symm.trans hb)
  let C := Classical.choice ((hν H hH).1 x hxsing)
  have hsing := (HilbertSamuel.normalizedHead_regular p x).2 hxsing
  refine ⟨HilbertSamuel.normalizedHead H.X x, hsing, ⟨x, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  by_cases hy : IsRegularLocalRing (H.X.presheaf.stalk y)
  · rw [(HilbertSamuel.normalizedHead_regular p y).1.mpr hy]
    exact hsing.le
  · let D := Classical.choice ((hν H hH).1 y hy)
    have hw : D.word ≤ C.word := calc
      D.word = ν H y := ((hν H hH).2.1 y D).2.symm
      _ ≤ m := hm.2 (Set.mem_range_self y)
      _ = ν H x := hx.symm
      _ = C.word := ((hν H hH).2.1 x C).2
    exact Prod.Lex.monotone_fst _ _ (WithBot.coe_le_coe.mp hw)

private theorem constant_tail_of_no_strict_drops {α : Type*} [LinearOrder α]
    (a : ℕ → α) (ha : Antitone a)
    (hno : ∀ f : ℕ → ℕ, ¬ ∀ k, a (f (k + 1)) < a (f k)) :
    ∃ n, ∀ k, a (n + k) = a n := by
  classical
  by_contra h
  have hdrop : ∀ n, ∃ m, a m < a n := by
    intro n
    by_contra hn
    push Not at hn
    apply h
    refine ⟨n, fun k ↦ le_antisymm (ha (Nat.le_add_right n k)) ?_⟩
    exact hn (n + k)
  choose next hnext using hdrop
  let f : ℕ → ℕ := Nat.rec 0 (fun _ j ↦ next j)
  exact hno f (fun k ↦ hnext (f k))

/-- There is no infinite sequence of these maximum-center extensions from an empty
initial history, for this fixed construction and this initial rational embedded pair.
Source: ILO VIII 2.3.11; node proof step 5
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: Progress gives geometry at every prefix, starting with the given embedded pair.
Greatest heads exist at all nonregular stages and are nonincreasing. Infinitely many strict
changes would give an infinite strictly decreasing chain of reachable heads from this one
input, excluded by the dimension-profile theorem. Otherwise there is a final infinite
constant-head interval, excluded by the synchronized marked-ideal argument. Regular or
empty stages admit no further maximum extension. No assertion about arbitrary descending
sequences in the whole value space is used. -/
theorem resolution_word_termination (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν) (A : EmbeddedResolutionPair.{u}) :
    ¬ ∃ (H : ∀ n : ℕ, EmbeddedResolutionHistory A n)
      (E : ∀ n : ℕ, Extension (H n) (H (n + 1))),
        ∀ n, IsMaximumStep ν (E n) := by
  classical
  rintro ⟨H, E, hE⟩
  have hadm : ∀ n, Admissible ν (H n) := by
    intro n
    induction n with
    | zero => exact .empty _
    | succ n ih => exact .step (E n) ih (hE n)
  have hmax : ∀ n, MaximumHistory ν (H n) := by
    intro n
    induction n with
    | zero => exact .empty _
    | succ n ih => exact .step (E n) ih (hE n)
  have hgeom : ∀ n, HasResolutionGeometry (H n) := by
    intro n
    induction n with
    | zero =>
      have : Smooth A.base := A.smooth
      have : IsSeparated A.base := A.separated
      have : LocallyOfFiniteType A.base := A.finiteType
      have : QuasiCompact A.base := A.quasiCompact
      have : IsReduced A.X := A.reduced
      have hb : (H 0).base = (H 0).initialAmbient.hom ≫ A.base := by
        change (H 0).ambient.map (𝟙 (op (0 : Fin 1))) ≫
          (H 0).initialAmbient.hom ≫ A.base = _
        rw [CategoryTheory.Functor.map_id]
        exact CategoryTheory.Category.id_comp _
      have hr : IsReduced (H 0).X :=
        isReduced_of_isOpenImmersion (H 0).initialIntrinsic.hom
      refine ⟨?_, ?_, ?_, ?_, hr⟩ <;> rw [hb] <;> infer_instance
    | succ n ih =>
      exact ((resolution_word_progress R ν hν (H n) (hadm n) ih).2 _ (E n) (hE n)).1
  choose a hsing hgreat using fun n ↦
    greatest_head_of_maximum_step R ν hν (hadm n) (hgeom n) (E n) (hE n)
  have hanti : Antitone a := antitone_nat_of_succ_le fun n ↦ by
    obtain ⟨x, hx⟩ := (hgreat (n + 1)).1
    rw [← hx]
    exact ((resolution_word_head_nonincrease R ν hν (hadm n) (hgeom n)
      (E n) (hE n)).1 x).trans ((hgreat n).2 (Set.mem_range_self _))
  have hno : ∀ f : ℕ → ℕ, ¬ ∀ k, a (f (k + 1)) < a (f k) := by
    intro f
    apply resolution_word_finitely_many_head_drops R ν hν A (a ∘ f)
    intro k
    exact ⟨f k, H (f k), hmax (f k), hgreat (f k)⟩
  obtain ⟨n, hn⟩ := constant_tail_of_no_strict_drops a hanti hno
  apply resolution_word_no_constant_head_tail R ν hν n
    (fun k ↦ H (n + k)) (fun k ↦ E (n + k)) (hadm n) (hgeom n)
    (fun k ↦ hE (n + k)) (a n) (hsing n)
  intro k
  rw [← hn k]
  exact hgreat (n + k)

/-- Regular and empty initial schemes have zero maximum extensions.
Source: ILO VIII 2.3.11, before exceptional cleanup; node proof step 6
(blueprint: lem-trf-resolution-word-progress-termination).

Proof: At a regular point the gluing assignment is bottom. An empty scheme has no points
and hence no word values. Neither case has an attained greatest value strictly above bottom,
as required by the definition of a maximum extension. Transport this fact through the
initial-history isomorphism. -/
theorem resolution_word_zero_extensions (R : MarkedIdeal.NumericalResolution.{u})
    (ν : ValueFamily.{u} HilbertSamuel.ResolutionWord)
    (hν : IsNormalizedResolutionWord R ν) (A : EmbeddedResolutionPair.{u})
    (hA : IsRegularScheme A.X ∨ IsEmpty A.X) (H : EmbeddedResolutionHistory A 0) :
    ∀ (K : EmbeddedResolutionHistory A 1) (E : Extension H K), ¬ IsMaximumStep ν E := by
  intro K E hE
  obtain ⟨m, hm, hpos, -⟩ := hE
  obtain ⟨x, hx⟩ := hm.1
  have hxreg : IsRegularLocalRing (H.X.presheaf.stalk x) := by
    rcases hA with hA | hA
    · have : IsRegular A.X := hA.2
      exact isRegularLocalRing_stalk_of_etale H.initialIntrinsic.hom
        (fun y ↦ IsRegular.isRegularLocalRing_stalk y) x
    · exact (hA.false (H.initialIntrinsic.hom x)).elim
  have hbot : ν H x = ⊥ := (hν H (.empty H)).2.2.2.2.1 x |>.mpr hxreg
  have : m = ⊥ := hx.symm.trans hbot
  exact (ne_of_gt hpos) this

end AlgebraicGeometry.EmbeddedResolutionHistory
