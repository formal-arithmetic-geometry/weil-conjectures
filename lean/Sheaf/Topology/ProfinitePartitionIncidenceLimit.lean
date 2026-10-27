module

public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Order

/-! # Profinite partition image incidence limits

Source: blueprint `det-pe-wc-cover-second-stage.proof.md`, Step 2, and
Stacks Project, Tag 097D, `lemma-construct-profinite`
(blueprint: lem-pe-profinite-partition-incidence-limit).

`DiscreteQuotient S` represents finite clopen partitions when S is compact: its
points are the nonempty clopen fibres of its surjective projection. Its order has
arrows from finer to coarser partitions, as required for the inverse system.
The inherited subtype and product topologies are used throughout, including for
an arbitrary space X without separation assumptions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open Topology

namespace ProfinitePartition

variable {S : Type u} {P : Type v} {X : Type w}
  [TopologicalSpace S] [TopologicalSpace P] [TopologicalSpace X]

/-- The image-incidence space for a partition, with the subspace topology of X × Q.
Its parts are the projection fibres; Q has Mathlib's discrete topology.
Source: blueprint `det-pe-wc-cover-second-stage`, Step 2; Stacks Tag 097D
(blueprint: lem-pe-profinite-partition-incidence-limit). -/
abbrev IncidenceStage (f : C(S, P)) (g : C(X, P)) (Q : DiscreteQuotient S) :=
  {z : X × Q // g z.1 ∈ f '' (Q.proj ⁻¹' {z.2})}

/-- Compatible incidence families, with the subspace topology of the product of stages.
The two equations say exactly that refinement preserves x and maps a fine part to
its containing coarse part. There is no restriction on the topology of X.
Source: blueprint `det-pe-wc-cover-second-stage`, Step 2; Stacks Tag 097D
(blueprint: lem-pe-profinite-partition-incidence-limit). -/
abbrev IncidenceLimit (f : C(S, P)) (g : C(X, P)) :=
  {y : (Q : DiscreteQuotient S) → IncidenceStage f g Q //
    ∀ (Q Q' : DiscreteQuotient S) (h : Q ≤ Q'),
      (y Q).val.1 = (y Q').val.1 ∧
        DiscreteQuotient.ofLE h (y Q).val.2 = (y Q').val.2}

/-- The canonical comparison from the pullback subspace: (x,s) maps to (x,Q.proj s)
at every partition. Incidence follows from g(x)=f(s), and compatibility is the
projection identity for refinement. All data are explicit.
Source: blueprint `det-pe-wc-cover-second-stage`, Step 2; Stacks Tag 097D
(blueprint: lem-pe-profinite-partition-incidence-limit). -/
def incidenceComparison (f : C(S, P)) (g : C(X, P)) :
    {z : X × S // g z.1 = f z.2} → IncidenceLimit f g :=
  fun z ↦ ⟨fun Q ↦ ⟨(z.val.1, Q.proj z.val.2), ⟨z.val.2, rfl, z.property.symm⟩⟩,
    fun _Q _Q' h ↦ ⟨rfl, DiscreteQuotient.ofLE_proj h z.val.2⟩⟩

/-- The canonical incidence comparison is a homeomorphism. Compatible parts intersect
in a unique point, their images intersect in its image, and the partition coordinates
jointly generate S's topology. Empty S or X makes both pullback and limit empty.

Source: blueprint `det-pe-wc-cover-second-stage.proof.md`, Step 2, paragraphs from
“A compatible family” through continuity of the map to S; Stacks Tags 097D, 005D,
and 08ZZ (blueprint: lem-pe-profinite-partition-incidence-limit).

Proof:
1. Discrete quotients form a small nonempty poset. Intersections give common
   refinements. Each quotient is finite by compactness; its fibres are precisely
   the nonempty clopen parts. Refinement preserves incidence by inclusion of fibres.
   If S is empty, every quotient has no points, and if X is empty, every stage is
   empty. The index has a top element, so the limit and pullback are empty in either case.
2. Partition projections are continuous. Every proper nonempty clopen V is a fibre
   of the partition {V, S minus V}. The clopen basis therefore proves the asserted
   equality of topologies; it also shows that partitions separate points.
3. For compatible parts, any finite collection contains a nonempty part from a
   common refinement. Compactness and closedness give a point in their intersection.
   Separation by partitions makes this point unique, and every point supplies its parts.
4. If p belongs to all images, the closed nonempty sets f inverse({p}) intersected
   with the chosen parts have the finite intersection property. Compactness gives
   a common point, necessarily the point s in step 3; hence p=f(s). The reverse
   inclusion is immediate. Closedness uses Hausdorff P and continuity of f.
5. A common refinement shows that all x coordinates of a compatible incidence
   family agree. Steps 3 and 4 recover its unique s with g(x)=f(s), giving a
   two-sided inverse to the displayed canonical comparison.
6. Each forward coordinate is continuous into X times the discrete quotient,
   hence into the incidence subspace. Product and subtype topologies give
   continuity of the comparison.
7. The inverse x coordinate is read from the coarsest partition. For a clopen V,
   its inverse s coordinate lies in V exactly when the chosen part at the
   partition {V, S minus V} is V. This is an open cylinder. The clopen basis
   gives continuity into S, and then continuity into the pullback subspace.
   This proves a homeomorphism without any separation hypothesis on X. -/
theorem profinitePartitionIncidenceLimit
    (S : Type u) (P : Type v) (X : Type w)
    [TopologicalSpace S] [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace S] [T2Space S] [TotallyDisconnectedSpace S]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (f : C(S, P)) (g : C(X, P)) :
    IsHomeomorph (incidenceComparison f g) ∧
      (∀ a : (Q : DiscreteQuotient S) → Q,
        (∀ (Q Q' : DiscreteQuotient S) (h : Q ≤ Q'),
          DiscreteQuotient.ofLE h (a Q) = a Q') →
        ∃! s : S,
          (⋂ Q : DiscreteQuotient S, Q.proj ⁻¹' {a Q}) = {s} ∧
            (⋂ Q : DiscreteQuotient S, f '' (Q.proj ⁻¹' {a Q})) = {f s}) ∧
      (‹TopologicalSpace S› =
        ⨅ Q : DiscreteQuotient S, TopologicalSpace.induced Q.proj inferInstance) ∧
      ((IsEmpty S ∨ IsEmpty X) →
        IsEmpty {z : X × S // g z.1 = f z.2} ∧ IsEmpty (IncidenceLimit f g)) := by
  classical
  let e : S → (Q : DiscreteQuotient S) → Q := fun s Q ↦ Q.proj s
  have hec : Continuous e := continuous_pi fun Q ↦ Q.proj_continuous
  have hei : Function.Injective e := fun s t h ↦
    DiscreteQuotient.eq_of_forall_proj_eq (fun Q ↦ congrFun h Q)
  have he : IsEmbedding e := (hec.isClosedEmbedding hei).isEmbedding
  have htop : ‹TopologicalSpace S› =
      ⨅ Q : DiscreteQuotient S, TopologicalSpace.induced Q.proj inferInstance := by
    simpa only [e, Pi.topologicalSpace, induced_iInf,
      induced_compose, Function.comp_def] using he.eq_induced
  have hinter (s : S) :
      (⋂ Q : DiscreteQuotient S, Q.proj ⁻¹' {Q.proj s}) = {s} := by
    ext t
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ DiscreteQuotient.eq_of_forall_proj_eq h, fun h Q ↦ congrArg Q.proj h⟩
  have himage (s : S) :
      (⋂ Q : DiscreteQuotient S, f '' (Q.proj ⁻¹' {Q.proj s})) = {f s} := by
    ext p
    constructor
    · intro hp
      let C : DiscreteQuotient S → Set S := fun Q ↦
        f ⁻¹' {p} ∩ Q.proj ⁻¹' {Q.proj s}
      have hclosed (Q : DiscreteQuotient S) : IsClosed (C Q) :=
        (isClosed_singleton.preimage f.continuous).inter (Q.isClosed_preimage _)
      have hnonempty (Q : DiscreteQuotient S) : (C Q).Nonempty := by
        obtain ⟨t, ht, hft⟩ := Set.mem_iInter.mp hp Q
        exact ⟨t, hft, ht⟩
      have hdir : Directed (· ⊇ ·) C := by
        intro Q R
        refine ⟨Q ⊓ R, ?_, ?_⟩
        · intro t ht
          exact ⟨ht.1, by
            have h := DiscreteQuotient.fiber_subset_ofLE
              (inf_le_left : Q ⊓ R ≤ Q) ((Q ⊓ R).proj s) ht.2
            simpa only [DiscreteQuotient.ofLE_proj] using h⟩
        · intro t ht
          exact ⟨ht.1, by
            have h := DiscreteQuotient.fiber_subset_ofLE
              (inf_le_right : Q ⊓ R ≤ R) ((Q ⊓ R).proj s) ht.2
            simpa only [DiscreteQuotient.ofLE_proj] using h⟩
      obtain ⟨t, ht⟩ :=
        IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir
          hnonempty (fun Q ↦ (hclosed Q).isCompact) hclosed
      have hts : t = s := DiscreteQuotient.eq_of_forall_proj_eq
        (fun Q ↦ (Set.mem_iInter.mp ht Q).2)
      exact (hts ▸ (Set.mem_iInter.mp ht ⊤).1).symm
    · intro hp
      subst p
      exact Set.mem_iInter.mpr fun Q ↦ ⟨s, rfl, rfl⟩
  have hparts : ∀ a : (Q : DiscreteQuotient S) → Q,
      (∀ (Q Q' : DiscreteQuotient S) (h : Q ≤ Q'),
        DiscreteQuotient.ofLE h (a Q) = a Q') →
      ∃! s : S,
        (⋂ Q : DiscreteQuotient S, Q.proj ⁻¹' {a Q}) = {s} ∧
          (⋂ Q : DiscreteQuotient S, f '' (Q.proj ⁻¹' {a Q})) = {f s} := by
    intro a ha
    obtain ⟨s, hs⟩ := DiscreteQuotient.exists_of_compat a ha
    have ha' : a = fun Q ↦ Q.proj s := funext fun Q ↦ (hs Q).symm
    subst a
    refine ⟨s, ⟨hinter s, himage s⟩, ?_⟩
    intro t ht
    have h : ({t} : Set S) = {s} := ht.1.symm.trans (hinter s)
    exact Set.singleton_injective h
  have hc : Continuous (incidenceComparison f g) := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro Q
    exact ((continuous_fst.comp continuous_subtype_val).prodMk
      (Q.proj_continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  have hinj : Function.Injective (incidenceComparison f g) := by
    intro z z' h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun y : IncidenceLimit f g ↦ (y.val ⊤).val.1) h
    · apply DiscreteQuotient.eq_of_forall_proj_eq
      intro Q
      exact congrArg (fun y : IncidenceLimit f g ↦ (y.val Q).val.2) h
  have hsurj : Function.Surjective (incidenceComparison f g) := by
    intro y
    obtain ⟨s, hs⟩ := DiscreteQuotient.exists_of_compat
      (fun Q ↦ (y.val Q).val.2) (fun Q R h ↦ (y.property Q R h).2)
    let x : X := (y.val ⊤).val.1
    have hx (Q : DiscreteQuotient S) : (y.val Q).val.1 = x :=
      (y.property Q ⊤ le_top).1
    have hfs : g x = f s := by
      apply Set.mem_singleton_iff.mp
      rw [← himage s]
      apply Set.mem_iInter.mpr
      intro Q
      rw [hs Q, ← hx Q]
      exact (y.val Q).property
    refine ⟨⟨(x, s), hfs⟩, ?_⟩
    apply Subtype.ext
    funext Q
    apply Subtype.ext
    exact Prod.ext (hx Q).symm (hs Q)
  let E := Equiv.ofBijective (incidenceComparison f g) ⟨hinj, hsurj⟩
  have hcoord (y : IncidenceLimit f g) (Q : DiscreteQuotient S) :
      (E.symm y).val.1 = (y.val Q).val.1 ∧
        Q.proj (E.symm y).val.2 = (y.val Q).val.2 := by
    have h := congrArg (fun z : IncidenceLimit f g ↦ (z.val Q).val)
      (E.apply_symm_apply y)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hcx : Continuous (fun y : IncidenceLimit f g ↦ (E.symm y).val.1) := by
    have hfun : (fun y : IncidenceLimit f g ↦ (E.symm y).val.1) =
        fun y ↦ (y.val ⊤).val.1 := funext fun y ↦ (hcoord y ⊤).1
    rw [hfun]
    exact continuous_fst.comp
      (continuous_subtype_val.comp ((continuous_apply ⊤).comp continuous_subtype_val))
  have hcs : Continuous (fun y : IncidenceLimit f g ↦ (E.symm y).val.2) := by
    apply he.continuous_iff.mpr
    apply continuous_pi
    intro Q
    have hfun : (fun y : IncidenceLimit f g ↦ e (E.symm y).val.2 Q) =
        fun y ↦ (y.val Q).val.2 := funext fun y ↦ (hcoord y Q).2
    change Continuous (fun y : IncidenceLimit f g ↦ e (E.symm y).val.2 Q)
    rw [hfun]
    exact continuous_snd.comp
      (continuous_subtype_val.comp ((continuous_apply Q).comp continuous_subtype_val))
  let H : {z : X × S // g z.1 = f z.2} ≃ₜ IncidenceLimit f g :=
    { toEquiv := E
      continuous_toFun := hc
      continuous_invFun := (hcx.prodMk hcs).subtype_mk _ }
  have hhomeo : IsHomeomorph (incidenceComparison f g) := H.isHomeomorph
  refine ⟨hhomeo, hparts, htop, ?_⟩
  intro hempty
  have hpb : IsEmpty {z : X × S // g z.1 = f z.2} := by
    constructor
    intro z
    rcases hempty with hS | hX
    · exact hS.false z.val.2
    · exact hX.false z.val.1
  refine ⟨hpb, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨z, _⟩ := hsurj y
  exact hpb.false z

end ProfinitePartition
