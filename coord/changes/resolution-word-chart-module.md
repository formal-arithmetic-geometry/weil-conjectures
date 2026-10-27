# AlgebraicGeometry.EmbeddedResolutionHistory.ResolutionWordChart

## Reason

The two geometric subarguments need the same existing chart definitions. Move those
unchanged declarations into a support module to avoid a cyclic import of the theorem that
combines the subarguments. The original module publicly re-exports the support module.
No existing declaration is removed or renamed, and no binder, field, definition body,
instance, or elaboration attribute changes. Only the blueprint tags identify the new
attachment. No target statement or definition meaning changes.

## Old

In `Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing`:

```lean
namespace AlgebraicGeometry.HilbertSamuel

/-- The fixed lexicographic head-and-tail space with one new least element.
Source: ILO VIII 2.3.11--2.3.13, node proof step 4
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
abbrev ResolutionWord := WithBot (DimensionHead ×ₗ MarkedIdeal.Word)

/-- Summation changes only the integer sequence in the head; the tail and bottom stay fixed.
Source: ILO VIII 2.3.13, node proof steps 1 and 9
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
def sumResolutionWord (D : ℕ) : ResolutionWord → ResolutionWord
  | none => none
  | some w => some (toLex (sumHead D (ofLex w).1, (ofLex w).2))

/-- The embedded scheme of a numerical input with its fresh test boundary empty.
The numerical input itself keeps its recorded exceptional boundary.
Source: ILO VIII 2.3.11--2.3.13, node proof step 3
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
def freshWordEmbedded (B : MarkedIdeal.{u}) : Embedded (ULift.{u} ℚ) :=
  { B.ambient with boundary := [] }

/-- The same ideal, support and marking, now tested with empty boundary.
Source: ILO VIII 2.3.11--2.3.13, node proof step 3
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
def freshWordMarked (B : MarkedIdeal.{u}) : Marked (freshWordEmbedded B) where
  N := B.marked.N
  j := B.marked.j
  closed := B.marked.closed
  smooth := B.marked.smooth
  ideal := B.marked.ideal
  coherent := B.marked.coherent
  marking := B.marked.marking
  positive := B.marked.positive

end AlgebraicGeometry.HilbertSamuel

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- The canonical map from the final strict transform to any preceding stage.
Source: ILO VIII 2.3.1, node proof step 5
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
def wordStageMap {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) (j : Fin (n + 1)) :
    H.X ⟶ H.intrinsic.obj (op j) :=
  H.intrinsic.map (homOfLE (Fin.le_last j)).op

/-- Earlier intrinsic center ideals, in chronological order, extended to a given stage.
Unlike the exceptional boundary, these use ordinary pullback, retaining identity blowups.
Source: ILO VIII 2.3.11--2.3.13, node proof steps 3 and 5
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
def wordEarlierCenters {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) :
    ∀ j : Fin (n + 1), List (H.intrinsic.obj (op j)).IdealSheafData :=
  Fin.induction [] (fun j L ↦
    L.map (fun I ↦ I.comap (H.intrinsic.map (homOfLE j.castSucc_le_succ).op)) ++
      [(H.centerToIntrinsic j).ker.comap
        (H.intrinsic.map (homOfLE j.castSucc_le_succ).op)])

/-- A local prescription of the word at a singular point. The numerical history covers
a suffix beginning at the first attainment of the current head along this pointed history.
Its strict transforms, centers and ordered boundary are compared by actual scheme maps and
ideal pullback. Old boundary members have relative birth zero, while their original absolute
births remain their positions in the full chronological boundary. A new presentation's finite
tests start empty, independently of that recorded history. Controlled transforms in the
suffix are exactly `MarkedIdeal.HistoryStep`, not independently chosen transformation maps.
Source: ILO VIII 2.3.11--2.3.13, node proof steps 3--5
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
structure ResolutionWordChart (R : MarkedIdeal.NumericalResolution.{u})
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n) (x : H.X) where
  singular : ¬ IsRegularLocalRing (H.X.presheaf.stalk x)
  length : ℕ
  history : MarkedIdeal.History.{u} length
  admissible : MarkedIdeal.Admissible R.value history
  index : Fin (length + 1) →o Fin (n + 1)
  consecutive : ∀ j, (index j).val = (index 0).val + j.val
  last : index (Fin.last length) = Fin.last n
  centerIndex : Fin length → Fin n
  centerSource : ∀ j, (centerIndex j).castSucc = index j.castSucc
  centerTarget : ∀ j, (centerIndex j).succ = index j.succ
  intrinsic : ∀ j, (history.state j).ambient.X ⟶ H.intrinsic.obj (op (index j))
  etale : ∀ j, Etale (intrinsic j)
  base : ∀ j, intrinsic j ≫
      H.intrinsic.map (homOfLE (Fin.zero_le (index j))).op ≫
      H.initialIntrinsic.hom ≫ A.inclusion ≫ A.base =
        (history.state j).ambient.i ≫ (history.state j).ambient.p
  point : ∀ j, (history.state j).ambient.X
  pointed : ∀ j, intrinsic j (point j) = H.wordStageMap (index j) x
  transition : ∀ j : Fin length,
    (history.state j.succ).ambient.X ⟶ (history.state j.castSucc).ambient.X
  transitionSquare : ∀ j, transition j ≫ (history.state j.castSucc).ambient.i =
    (history.state j.succ).ambient.i ≫ (history.step j).step.π
  transitionPoint : ∀ j, transition j (point j.succ) = point j.castSucc
  naturality : ∀ j, transition j ≫ intrinsic j.castSucc =
    intrinsic j.succ ≫ H.intrinsic.map
      (homOfLE (index.monotone j.castSucc_le_succ)).op
  centers : ∀ j,
    (history.step j).step.center.comap (history.state j.castSucc).ambient.i =
      (H.centerToIntrinsic (centerIndex j)).ker.comap
        (intrinsic j.castSucc ≫ eqToHom
          (congrArg (fun k ↦ H.intrinsic.obj (op k)) (centerSource j).symm))
  earlier : ∀ j, List (history.state j).ambient.Z.IdealSheafData
  earlierPullback : ∀ j,
    (earlier j).map (fun I ↦ I.comap (history.state j).ambient.i) =
      (H.wordEarlierCenters (index j)).map (fun I ↦ I.comap (intrinsic j))
  boundary : ∀ j,
    (history.state j).ambient.boundary.map
        (fun I ↦ I.comap (history.state j).ambient.i) =
      (H.coefficientHistoryBoundary (index j)).map (fun I ↦ I.comap (intrinsic j))
  births : ∀ (j : Fin (length + 1))
    (k : Fin (history.state j).ambient.boundary.length),
    history.birth j k = k.val + 1 - (index 0).val
  minimal : HilbertSamuel.MinimalAt
    (HilbertSamuel.freshWordEmbedded (history.state 0)) (point 0)
  level : (history.state 0).ambient.level =
    HilbertSamuel.function
      ((history.state 0).ambient.i ≫ (history.state 0).ambient.p) (point 0)
  presents : HilbertSamuel.Presents (HilbertSamuel.freshWordMarked (history.state 0))
  maximal : HilbertSamuel.FullMaximalOrder (HilbertSamuel.freshWordMarked (history.state 0))
  maximalStages : ∀ j, (history.state j).IsMaximalOrder
  retainedHead : ∀ j,
    HilbertSamuel.normalizedHead (history.state j).ambient.X (point j) =
      HilbertSamuel.normalizedHead H.X x
  firstHead : ∀ j : Fin (n + 1), j < index 0 →
    HilbertSamuel.normalizedHead (H.intrinsic.obj (op j)) (H.wordStageMap j x) ≠
      HilbertSamuel.normalizedHead H.X x
  supportPoint : history.last.marked.N
  cosupport : supportPoint ∈ history.last.cosupport
  supportInclusion : history.last.marked.j supportPoint =
    history.last.ambient.i (point (Fin.last length))

/-- Delete the leading one from the fixed engine word of the specified controlled history.
Source: ILO VIII 2.3.11--2.3.13, node proof step 4
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
def ResolutionWordChart.tail {R : MarkedIdeal.NumericalResolution.{u}}
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} {H : EmbeddedResolutionHistory A n} {x : H.X}
    (C : ResolutionWordChart R H x) : MarkedIdeal.Word :=
  (R.value C.history ⟨C.supportPoint, C.cosupport⟩).drop 1

/-- The normalized head followed by the actual local numerical tail.
Source: ILO VIII 2.3.11--2.3.13, node proof step 4
(blueprint: lem-trf-normalized-resolution-word-gluing). -/
def ResolutionWordChart.word {R : MarkedIdeal.NumericalResolution.{u}}
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} {H : EmbeddedResolutionHistory A n} {x : H.X}
    (C : ResolutionWordChart R H x) : HilbertSamuel.ResolutionWord :=
  some (toLex (HilbertSamuel.normalizedHead H.X x, C.tail))

```

## New

The same declarations in `Sheaf.AlgebraicGeometry.NormalizedResolutionWordCharts`,
with their blueprint tags changed to `def-trf-resolution-word-charts`:

```lean
namespace AlgebraicGeometry.HilbertSamuel

/-- The fixed lexicographic head-and-tail space with one new least element.
Source: ILO VIII 2.3.11--2.3.13, node proof step 4
(blueprint: def-trf-resolution-word-charts). -/
abbrev ResolutionWord := WithBot (DimensionHead ×ₗ MarkedIdeal.Word)

/-- Summation changes only the integer sequence in the head; the tail and bottom stay fixed.
Source: ILO VIII 2.3.13, node proof steps 1 and 9
(blueprint: def-trf-resolution-word-charts). -/
def sumResolutionWord (D : ℕ) : ResolutionWord → ResolutionWord
  | none => none
  | some w => some (toLex (sumHead D (ofLex w).1, (ofLex w).2))

/-- The embedded scheme of a numerical input with its fresh test boundary empty.
The numerical input itself keeps its recorded exceptional boundary.
Source: ILO VIII 2.3.11--2.3.13, node proof step 3
(blueprint: def-trf-resolution-word-charts). -/
def freshWordEmbedded (B : MarkedIdeal.{u}) : Embedded (ULift.{u} ℚ) :=
  { B.ambient with boundary := [] }

/-- The same ideal, support and marking, now tested with empty boundary.
Source: ILO VIII 2.3.11--2.3.13, node proof step 3
(blueprint: def-trf-resolution-word-charts). -/
def freshWordMarked (B : MarkedIdeal.{u}) : Marked (freshWordEmbedded B) where
  N := B.marked.N
  j := B.marked.j
  closed := B.marked.closed
  smooth := B.marked.smooth
  ideal := B.marked.ideal
  coherent := B.marked.coherent
  marking := B.marked.marking
  positive := B.marked.positive

end AlgebraicGeometry.HilbertSamuel

namespace AlgebraicGeometry.EmbeddedResolutionHistory

/-- The canonical map from the final strict transform to any preceding stage.
Source: ILO VIII 2.3.1, node proof step 5
(blueprint: def-trf-resolution-word-charts). -/
def wordStageMap {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) (j : Fin (n + 1)) :
    H.X ⟶ H.intrinsic.obj (op j) :=
  H.intrinsic.map (homOfLE (Fin.le_last j)).op

/-- Earlier intrinsic center ideals, in chronological order, extended to a given stage.
Unlike the exceptional boundary, these use ordinary pullback, retaining identity blowups.
Source: ILO VIII 2.3.11--2.3.13, node proof steps 3 and 5
(blueprint: def-trf-resolution-word-charts). -/
def wordEarlierCenters {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) :
    ∀ j : Fin (n + 1), List (H.intrinsic.obj (op j)).IdealSheafData :=
  Fin.induction [] (fun j L ↦
    L.map (fun I ↦ I.comap (H.intrinsic.map (homOfLE j.castSucc_le_succ).op)) ++
      [(H.centerToIntrinsic j).ker.comap
        (H.intrinsic.map (homOfLE j.castSucc_le_succ).op)])

/-- A local prescription of the word at a singular point. The numerical history covers
a suffix beginning at the first attainment of the current head along this pointed history.
Its strict transforms, centers and ordered boundary are compared by actual scheme maps and
ideal pullback. Old boundary members have relative birth zero, while their original absolute
births remain their positions in the full chronological boundary. A new presentation's finite
tests start empty, independently of that recorded history. Controlled transforms in the
suffix are exactly `MarkedIdeal.HistoryStep`, not independently chosen transformation maps.
Source: ILO VIII 2.3.11--2.3.13, node proof steps 3--5
(blueprint: def-trf-resolution-word-charts). -/
structure ResolutionWordChart (R : MarkedIdeal.NumericalResolution.{u})
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n) (x : H.X) where
  singular : ¬ IsRegularLocalRing (H.X.presheaf.stalk x)
  length : ℕ
  history : MarkedIdeal.History.{u} length
  admissible : MarkedIdeal.Admissible R.value history
  index : Fin (length + 1) →o Fin (n + 1)
  consecutive : ∀ j, (index j).val = (index 0).val + j.val
  last : index (Fin.last length) = Fin.last n
  centerIndex : Fin length → Fin n
  centerSource : ∀ j, (centerIndex j).castSucc = index j.castSucc
  centerTarget : ∀ j, (centerIndex j).succ = index j.succ
  intrinsic : ∀ j, (history.state j).ambient.X ⟶ H.intrinsic.obj (op (index j))
  etale : ∀ j, Etale (intrinsic j)
  base : ∀ j, intrinsic j ≫
      H.intrinsic.map (homOfLE (Fin.zero_le (index j))).op ≫
      H.initialIntrinsic.hom ≫ A.inclusion ≫ A.base =
        (history.state j).ambient.i ≫ (history.state j).ambient.p
  point : ∀ j, (history.state j).ambient.X
  pointed : ∀ j, intrinsic j (point j) = H.wordStageMap (index j) x
  transition : ∀ j : Fin length,
    (history.state j.succ).ambient.X ⟶ (history.state j.castSucc).ambient.X
  transitionSquare : ∀ j, transition j ≫ (history.state j.castSucc).ambient.i =
    (history.state j.succ).ambient.i ≫ (history.step j).step.π
  transitionPoint : ∀ j, transition j (point j.succ) = point j.castSucc
  naturality : ∀ j, transition j ≫ intrinsic j.castSucc =
    intrinsic j.succ ≫ H.intrinsic.map
      (homOfLE (index.monotone j.castSucc_le_succ)).op
  centers : ∀ j,
    (history.step j).step.center.comap (history.state j.castSucc).ambient.i =
      (H.centerToIntrinsic (centerIndex j)).ker.comap
        (intrinsic j.castSucc ≫ eqToHom
          (congrArg (fun k ↦ H.intrinsic.obj (op k)) (centerSource j).symm))
  earlier : ∀ j, List (history.state j).ambient.Z.IdealSheafData
  earlierPullback : ∀ j,
    (earlier j).map (fun I ↦ I.comap (history.state j).ambient.i) =
      (H.wordEarlierCenters (index j)).map (fun I ↦ I.comap (intrinsic j))
  boundary : ∀ j,
    (history.state j).ambient.boundary.map
        (fun I ↦ I.comap (history.state j).ambient.i) =
      (H.coefficientHistoryBoundary (index j)).map (fun I ↦ I.comap (intrinsic j))
  births : ∀ (j : Fin (length + 1))
    (k : Fin (history.state j).ambient.boundary.length),
    history.birth j k = k.val + 1 - (index 0).val
  minimal : HilbertSamuel.MinimalAt
    (HilbertSamuel.freshWordEmbedded (history.state 0)) (point 0)
  level : (history.state 0).ambient.level =
    HilbertSamuel.function
      ((history.state 0).ambient.i ≫ (history.state 0).ambient.p) (point 0)
  presents : HilbertSamuel.Presents (HilbertSamuel.freshWordMarked (history.state 0))
  maximal : HilbertSamuel.FullMaximalOrder (HilbertSamuel.freshWordMarked (history.state 0))
  maximalStages : ∀ j, (history.state j).IsMaximalOrder
  retainedHead : ∀ j,
    HilbertSamuel.normalizedHead (history.state j).ambient.X (point j) =
      HilbertSamuel.normalizedHead H.X x
  firstHead : ∀ j : Fin (n + 1), j < index 0 →
    HilbertSamuel.normalizedHead (H.intrinsic.obj (op j)) (H.wordStageMap j x) ≠
      HilbertSamuel.normalizedHead H.X x
  supportPoint : history.last.marked.N
  cosupport : supportPoint ∈ history.last.cosupport
  supportInclusion : history.last.marked.j supportPoint =
    history.last.ambient.i (point (Fin.last length))

/-- Delete the leading one from the fixed engine word of the specified controlled history.
Source: ILO VIII 2.3.11--2.3.13, node proof step 4
(blueprint: def-trf-resolution-word-charts). -/
def ResolutionWordChart.tail {R : MarkedIdeal.NumericalResolution.{u}}
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} {H : EmbeddedResolutionHistory A n} {x : H.X}
    (C : ResolutionWordChart R H x) : MarkedIdeal.Word :=
  (R.value C.history ⟨C.supportPoint, C.cosupport⟩).drop 1

/-- The normalized head followed by the actual local numerical tail.
Source: ILO VIII 2.3.11--2.3.13, node proof step 4
(blueprint: def-trf-resolution-word-charts). -/
def ResolutionWordChart.word {R : MarkedIdeal.NumericalResolution.{u}}
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} {H : EmbeddedResolutionHistory A n} {x : H.X}
    (C : ResolutionWordChart R H x) : HilbertSamuel.ResolutionWord :=
  some (toLex (HilbertSamuel.normalizedHead H.X x, C.tail))

```

The original module re-exports these declarations with:

```lean
public import Sheaf.AlgebraicGeometry.NormalizedResolutionWordCharts
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing | A3 | Uses the same declarations through their public re-export; theorem statement unchanged. |
| Sheaf.AlgebraicGeometry.ResolutionWordFiniteHistoryComparison | no local claim record | Existing direct importer; statements and proofs require no adaptation. |
| Sheaf.AlgebraicGeometry.ResolutionWordMaximumCenterDescent | no local claim record | Existing direct importer; statements and proofs require no adaptation. |
| Sheaf.AlgebraicGeometry.ResolutionWordProgressTermination | no local claim record | Existing direct importer; statements and proofs require no adaptation. |
| Sheaf.AlgebraicGeometry.ResolutionInvariantCalculus | no local claim record | Transitive consumer mentioning ResolutionWord; its definition is unchanged and re-exported. |
| Sheaf.AlgebraicGeometry.EmbeddedResolutionAmbientComparison | no local claim record | Transitive consumer; no signature or behavior change. |
| Sheaf.AlgebraicGeometry.SmoothFunctorialNormalizedToricDesingularization | no local claim record | Transitive consumer; no signature or behavior change. |
| Sheaf.AlgebraicGeometry.SmoothFunctorialOrdinaryResolution | no local claim record | Transitive consumer; no signature or behavior change. |
| Sheaf.RingTheory.CompleteToricFaceStrata | no local claim record | Transitive consumer; no signature or behavior change. |
| Sheaf.AlgebraicGeometry.ResolutionWordCoherentPrescription | new in this delivery | States chart existence and compatibility using the relocated definitions. |
| Sheaf.AlgebraicGeometry.ResolutionWordFiniteLocalUpperBounds | new in this delivery | States the topological descent argument using the relocated definitions. |

The direct-importer set is the three ResolutionWord consumer modules above. Each was
compiled against the delivered module and support files, and its unchanged copy was removed
from the sandbox. The refreshed `tools/downstream.py --uses ResolutionWord` reports eight
transitive consumers; all are listed, including ResolutionInvariantCalculus, which mentions
the moved alphabet. Their imported declarations retain identical names and definition bodies.
No existing consumer requires adaptation.

## Status

landed 20261026T091036-L-3301601 2026-10-26 (merge of deliver/A3/Sheaf.AlgebraicGeometry.NormalizedResolutionWordGluing)
