/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent
public import Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage
public import Sheaf.RingTheory.FilteredColimitFiniteData
import Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage
import Sheaf.Order.DirectedFiniteUpperBound

/-!
# The common equality stage of a relative gluing datum

Source: Weil conjectures blueprint, sec-nagata-compactification, node order 360;
Stacks Project, Tag 01ZM, proof (blueprint: def-nagata-relative-gluing-valid-stage).

The finite lists below spell out the required equations on the finite basic overlap
pieces. Pairwise agreement allows the piece maps to glue; opposite orientations and
inverse identities give the inverse transition; the domain and map equations on triples
are the cocycle. Equality choices retain the preceding constructions' actual inputs.
No gluing axiom at the selected stage is assumed here.
-/

@[expose] public section

universe u

set_option genInjectivity false
set_option genSizeOf false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f)

/-- The canonical raw chart over the raw base. Source: blueprint order 360
(blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeRawChart (j : Σ a, R.base.base.chartIndex a) :
    Over (D.obj (op R.raw.stage)) :=
  Over.mk (pullback.snd (R.charts.chartMap j)
    (D.map (homOfLE ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op))

/-- The canonical raw left overlap over the raw base. Source: blueprint order 360
(blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeRawLeft (j k : Σ a, R.base.base.chartIndex a)
    (l : R.base.base.overlapIndex j k) : Over (D.obj (op R.raw.stage)) :=
  Over.mk (pullback.snd (R.schemes.leftMap j k l)
    (D.map (homOfLE R.raw.overlap_le_raw).op))

/-- The canonical raw right overlap over the raw base. Source: blueprint order 360
(blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeRawRight (j k : Σ a, R.base.base.chartIndex a)
    (l : R.base.base.overlapIndex j k) : Over (D.obj (op R.raw.stage)) :=
  Over.mk (pullback.snd (R.schemes.rightMap j k l)
    (D.map (homOfLE R.raw.overlap_le_raw).op))

/-- Canonical inclusions of the transported overlap schemes into the raw charts.
The projection equations, together with the over-base typing, uniquely determine the
maps by the pullback universal property. These are reassociation comparisons, not new
choices of overlap maps. Source: blueprint order 360, Tag 01ZM proof
(blueprint: def-nagata-relative-gluing-valid-stage). -/
structure NagataRelativeRawInclusions where
  left : ∀ j k l, nagataRelativeRawLeft D c hc i₀ f R j k l ⟶
    nagataRelativeRawChart D c hc i₀ f R j
  left_fst : ∀ j k l, (left j k l).left ≫ pullback.fst (R.charts.chartMap j)
    (D.map (homOfLE ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op) =
      pullback.fst (R.schemes.leftMap j k l)
        (D.map (homOfLE R.raw.overlap_le_raw).op) ≫
      eqToHom (R.schemes.leftScheme_eq j k l) ≫ (R.stages.leftAtOverlap j k l).ι ≫
      pullback.fst (R.charts.chartMap j) (D.map (homOfLE (R.stages.chart_le_overlap j)).op)
  right : ∀ j k l, nagataRelativeRawRight D c hc i₀ f R j k l ⟶
    nagataRelativeRawChart D c hc i₀ f R k
  right_fst : ∀ j k l, (right j k l).left ≫ pullback.fst (R.charts.chartMap k)
    (D.map (homOfLE ((R.stages.chart_le_overlap k).trans R.raw.overlap_le_raw)).op) =
      pullback.fst (R.schemes.rightMap j k l)
        (D.map (homOfLE R.raw.overlap_le_raw).op) ≫
      eqToHom (R.schemes.rightScheme_eq j k l) ≫ (R.stages.rightAtOverlap j k l).ι ≫
      pullback.fst (R.charts.chartMap k) (D.map (homOfLE (R.stages.chart_le_overlap k)).op)

/-- A pair of parallel maps over a fixed base, used only as an entry in the explicitly
computed relation list. Source: blueprint order 360
(blueprint: def-nagata-relative-gluing-valid-stage). -/
structure NagataRelativeMapRelation (S : Scheme.{u}) where
  source : Over S
  target : Over S
  phi : source ⟶ target
  psi : source ⟶ target

/-- A pair of opens in one scheme over the raw base, used as an entry in the explicitly
computed domain relation list. Source: blueprint order 360
(blueprint: def-nagata-relative-gluing-valid-stage). -/
structure NagataRelativeOpenRelation (S : Scheme.{u}) where
  source : Over S
  first : source.left.Opens
  second : source.left.Opens

variable (P : NagataRelativeRawInclusions D c hc i₀ f R)

/-- The forward map of a raw overlap, followed by its target-chart inclusion.
Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeForwardToChart (j k : Σ a, R.base.base.chartIndex a)
    (l : R.base.base.overlapIndex j k) : nagataRelativeRawLeft D c hc i₀ f R j k l ⟶
      nagataRelativeRawChart D c hc i₀ f R k :=
  (R.raw.forwardRaw j k l).map ≫ P.right j k l

/-- The backward map of a raw overlap, followed by its source-chart inclusion.
Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeBackwardToChart (j k : Σ a, R.base.base.chartIndex a)
    (l : R.base.base.overlapIndex j k) : nagataRelativeRawRight D c hc i₀ f R j k l ⟶
      nagataRelativeRawChart D c hc i₀ f R j :=
  (R.raw.backwardRaw j k l).map ≫ P.left j k l

/-- The finite map relations: both inverse identities on every piece; agreement of
forward maps on intersections of pieces, agreement of backward maps on intersections,
and agreement with the reversed orientation; diagonal identity; triple cocycle on the
intersection with every direct overlap piece. All sources and targets are canonical
pullbacks over the raw base. Source: blueprint order 360, Tag 01ZM proof
(blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeMapRelations :
    List (NagataRelativeMapRelation (D.obj (op R.raw.stage))) := by
  classical
  letI := R.base.base.finiteBase
  letI := R.base.base.finiteCharts
  letI := R.base.base.finiteOverlaps
  letI := Fintype.ofFinite (Σ a, R.base.base.chartIndex a)
  letI := fun j k ↦ Fintype.ofFinite (R.base.base.overlapIndex j k)
  let js := (Finset.univ : Finset (Σ a, R.base.base.chartIndex a)).toList
  let ls := fun j k ↦ (Finset.univ : Finset (R.base.base.overlapIndex j k)).toList
  let a := P.left
  let b := P.right
  let g := nagataRelativeForwardToChart D c hc i₀ f R P
  let h := nagataRelativeBackwardToChart D c hc i₀ f R P
  exact (js.flatMap fun j ↦ js.flatMap fun k ↦ (ls j k).flatMap fun l ↦
    [⟨_, _, (R.raw.forwardRaw j k l).map ≫ (R.raw.backwardRaw j k l).map, 𝟙 _⟩,
     ⟨_, _, (R.raw.backwardRaw j k l).map ≫ (R.raw.forwardRaw j k l).map, 𝟙 _⟩] ++
    ((ls j k).flatMap fun m ↦
      [⟨_, _, pullback.fst (a j k l) (a j k m) ≫ g j k l,
        pullback.snd (a j k l) (a j k m) ≫ g j k m⟩,
       ⟨_, _, pullback.fst (b j k l) (b j k m) ≫ h j k l,
        pullback.snd (b j k l) (b j k m) ≫ h j k m⟩]) ++
    ((ls k j).map fun m ↦
      ⟨_, _, pullback.fst (a j k l) (b k j m) ≫ g j k l,
        pullback.snd (a j k l) (b k j m) ≫ h k j m⟩)) ++
    (js.flatMap fun j ↦ (ls j j).map fun l ↦ ⟨_, _, a j j l, g j j l⟩) ++
    (js.flatMap fun j ↦ js.flatMap fun k ↦ js.flatMap fun z ↦
      (ls j k).flatMap fun l ↦ (ls k z).flatMap fun m ↦ (ls j z).map fun n ↦
        ⟨_, _, pullback.fst
          (pullback.fst (g j k l) (a k z m) ≫ a j k l) (a j z n) ≫
          pullback.snd (g j k l) (a k z m) ≫ g k z m,
        pullback.snd (pullback.fst (g j k l) (a k z m) ≫ a j k l) (a j z n) ≫
          g j z n⟩)

/-- The finite domain relations: diagonal overlap covers its chart; the union of left
pieces equals the union of right pieces for the reversed orientation; and on each first
piece the domain of a two-step transition equals the direct-transition domain.
Source: blueprint order 360, Tag 01ZM proof
(blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeOpenRelations :
    List (NagataRelativeOpenRelation (D.obj (op R.raw.stage))) := by
  classical
  letI := R.base.base.finiteBase
  letI := R.base.base.finiteCharts
  letI := R.base.base.finiteOverlaps
  letI := Fintype.ofFinite (Σ a, R.base.base.chartIndex a)
  letI := fun j k ↦ Fintype.ofFinite (R.base.base.overlapIndex j k)
  let js := (Finset.univ : Finset (Σ a, R.base.base.chartIndex a)).toList
  let ls := fun j k ↦ (Finset.univ : Finset (R.base.base.overlapIndex j k)).toList
  let w := fun j k ↦ ⨆ l, R.raw.rawLeftOpen j k l
  let v := fun j k ↦ ⨆ l, R.raw.rawRightOpen j k l
  exact (js.map fun j ↦ ⟨nagataRelativeRawChart D c hc i₀ f R j, w j j, ⊤⟩) ++
    (js.flatMap fun j ↦ js.map fun k ↦
      ⟨nagataRelativeRawChart D c hc i₀ f R j, w j k, v k j⟩) ++
    (js.flatMap fun j ↦ js.flatMap fun k ↦ js.flatMap fun z ↦ (ls j k).map fun l ↦
      ⟨nagataRelativeRawLeft D c hc i₀ f R j k l,
        (nagataRelativeForwardToChart D c hc i₀ f R P j k l).left ⁻¹ᵁ w k z,
        (P.left j k l).left ⁻¹ᵁ w j z⟩)

/-- Inputs for the recorded compact-open equality construction for one domain relation.
The limit equality is an equality of the specified opens, not an arbitrary witness stage.
Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
structure NagataRelativeOpenEqualityChoice
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (s : I)
    (e : NagataRelativeOpenRelation (D.obj (op s))) where
  [compactSource : CompactSpace e.source.left]
  [qsSource : QuasiSeparatedSpace e.source.left]
  compactFirst : IsCompact (e.first : Set e.source.left)
  compactSecond : IsCompact (e.second : Set e.source.left)
  limit_eq : pullback.fst e.source.hom (c.π.app (op s)) ⁻¹ᵁ e.first =
    pullback.fst e.source.hom (c.π.app (op s)) ⁻¹ᵁ e.second

/-- Inputs for the recorded morphism-equality construction for one explicitly computed
parallel pair. The affine covers, generators and coefficient witnesses are precisely
`NagataMorphismEqualityStageData`, including its equality on the limit.
Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
structure NagataRelativeMapEqualityChoice
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (s : I) (e : NagataRelativeMapRelation (D.obj (op s)))
    (d : I → I → I) (r : LinearOrder I) where
  [compactBase : CompactSpace (D.obj (op s))]
  [qsBase : QuasiSeparatedSpace (D.obj (op s))]
  [compactSource : CompactSpace e.source.left]
  [qsSource : QuasiSeparatedSpace e.source.left]
  [lfpSource : LocallyOfFinitePresentation e.source.hom]
  [qcSource : QuasiCompact e.source.hom]
  [qsSourceMap : QuasiSeparated e.source.hom]
  [lfpTarget : LocallyOfFinitePresentation e.target.hom]
  [qcTarget : QuasiCompact e.target.hom]
  [qsTargetMap : QuasiSeparated e.target.hom]
  choice : NagataMorphismEqualityStageData D c hc s e.source.hom e.target.hom
    e.phi.left e.psi.left e.phi.w e.psi.w d r

/-- The selected stage for one specified domain equation, using the preceding compact-open
construction. Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeOpenEqualityStage
    {s : I} {e : NagataRelativeOpenRelation (D.obj (op s))}
    (a : NagataRelativeOpenEqualityChoice D c s e) (d : I → I → I) (r : LinearOrder I) : I := by
  letI := a.compactSource
  letI := a.qsSource
  exact nagataQCOpenEqualityStage D c hc s e.source.hom e.first e.second
    a.compactFirst a.compactSecond a.limit_eq d r

/-- The selected stage for one specified map equation, using the preceding morphism-equality
construction. Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeMapEqualityStage
    {s : I} {e : NagataRelativeMapRelation (D.obj (op s))}
    {d : I → I → I} {r : LinearOrder I}
    (a : NagataRelativeMapEqualityChoice D c hc s e d r) : I := by
  letI := a.compactBase
  letI := a.qsBase
  letI := a.compactSource
  letI := a.qsSource
  letI := a.lfpSource
  letI := a.qcSource
  letI := a.qsSourceMap
  letI := a.lfpTarget
  letI := a.qcTarget
  letI := a.qsTargetMap
  exact nagataMorphismEqualityStage a.choice

/-- One choice for every entry of the computed finite lists, with the fixed binary upper
bounds and linear enumeration order of the raw datum. No finite-stage gluing identities
are assumed. Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
structure NagataRelativeGluingValidStageData where
  opens : ∀ n : Fin (nagataRelativeOpenRelations D c hc i₀ f R P).length,
    NagataRelativeOpenEqualityChoice D c R.raw.stage
      ((nagataRelativeOpenRelations D c hc i₀ f R P).get n)
  maps : ∀ n : Fin (nagataRelativeMapRelations D c hc i₀ f R P).length,
    NagataRelativeMapEqualityChoice D c hc R.raw.stage
      ((nagataRelativeMapRelations D c hc i₀ f R P).get n) R.base.boundPair R.base.boundOrder

variable (A : NagataRelativeGluingValidStageData D c hc i₀ f R P)

open Classical in
/-- The finite set of the raw stage and all selected domain and map equality stages.
Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeGluingEqualityStages : Finset I :=
  insert R.raw.stage
    ((Finset.univ.image fun n ↦ nagataRelativeOpenEqualityStage D c hc (A.opens n)
      R.base.boundPair R.base.boundOrder) ∪
     (Finset.univ.image fun n ↦ nagataRelativeMapEqualityStage D c hc (A.maps n)))

/-- The selected common upper bound defining lambda_rel, using exactly the raw stage and
all equality stages in the two finite lists. Source: blueprint order 360, Tag 01ZM proof
(blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeGluingValidStage : I :=
  directedFiniteUpperBound i₀ R.base.boundPair R.base.boundOrder
    (nagataRelativeGluingEqualityStages D c hc i₀ f R P A)

/-- The raw stage is below the selected stage; this proof is used only to type transport.
Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage).
Proof: the raw stage is inserted into `nagataRelativeGluingEqualityStages`. Apply
`le_directedFiniteUpperBound` with the raw datum's fixed `boundPair_le`. -/
theorem nagataRelativeRawStage_le_validStage :
    R.raw.stage ≤ nagataRelativeGluingValidStage D c hc i₀ f R P A := by
  sorry

/-- The transported finite diagram, including chart and overlap schemes over the new base,
opens in the charts, both inclusions, and both directions of each overlap map.
Source: blueprint order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
structure NagataRelativeGluingTransport (S : Scheme.{u}) (J : Type u)
    (K : J → J → Type u) where
  chart : J → Over S
  left : ∀ j k, K j k → Over S
  right : ∀ j k, K j k → Over S
  leftOpen : ∀ j k, K j k → (chart j).left.Opens
  rightOpen : ∀ j k, K j k → (chart k).left.Opens
  leftInclusion : ∀ j k l, left j k l ⟶ chart j
  rightInclusion : ∀ j k l, right j k l ⟶ chart k
  forward : ∀ j k l, left j k l ⟶ right j k l
  backward : ∀ j k l, right j k l ⟶ left j k l

/-- Canonical transport to any later stage. `Over.pullback` transports each arrow with
its source and target; the same functor transports both sides of every parallel equation.
The opens are inverse images under the canonical chart projections. Source: blueprint
order 360 (blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeGluingAtStage (t : I) (ht : R.raw.stage ≤ t) :
    NagataRelativeGluingTransport (D.obj (op t)) (Σ a, R.base.base.chartIndex a)
      R.base.base.overlapIndex :=
  { chart := fun j ↦ (Over.pullback (D.map (homOfLE ht).op)).obj
      (nagataRelativeRawChart D c hc i₀ f R j)
    left := fun j k l ↦ (Over.pullback (D.map (homOfLE ht).op)).obj
      (nagataRelativeRawLeft D c hc i₀ f R j k l)
    right := fun j k l ↦ (Over.pullback (D.map (homOfLE ht).op)).obj
      (nagataRelativeRawRight D c hc i₀ f R j k l)
    leftOpen := fun j k l ↦ pullback.fst
      (nagataRelativeRawChart D c hc i₀ f R j).hom
      (D.map (homOfLE ht).op) ⁻¹ᵁ R.raw.rawLeftOpen j k l
    rightOpen := fun j k l ↦ pullback.fst
      (nagataRelativeRawChart D c hc i₀ f R k).hom
      (D.map (homOfLE ht).op) ⁻¹ᵁ R.raw.rawRightOpen j k l
    leftInclusion := fun j k l ↦ (Over.pullback (D.map (homOfLE ht).op)).map (P.left j k l)
    rightInclusion := fun j k l ↦ (Over.pullback (D.map (homOfLE ht).op)).map (P.right j k l)
    forward := fun j k l ↦ (Over.pullback (D.map (homOfLE ht).op)).map
      (R.raw.forwardRaw j k l).map
    backward := fun j k l ↦ (Over.pullback (D.map (homOfLE ht).op)).map
      (R.raw.backwardRaw j k l).map }

/-- The named relative datum at lambda_rel, defined by canonical transport, retaining
all fixed earlier choices. Source: blueprint order 360
(blueprint: def-nagata-relative-gluing-valid-stage). -/
noncomputable def nagataRelativeGluingValidDatum :
    NagataRelativeGluingTransport
      (D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))
      (Σ a, R.base.base.chartIndex a) R.base.base.overlapIndex :=
  nagataRelativeGluingAtStage D c hc i₀ f R P
    (nagataRelativeGluingValidStage D c hc i₀ f R P A)
    (nagataRelativeRawStage_le_validStage D c hc i₀ f R P A)

end AlgebraicGeometry
