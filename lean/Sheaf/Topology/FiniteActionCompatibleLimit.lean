module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Compatible-family limits of finite continuous actions

Source: Stacks Project, Tags 08ZU, 08ZV, 08ZY and the product/subspace description
preceding Tag 0A2P; Bhatt–Scholze, Example 4.1.10, p. 28, coordinate-action expansion.
(blueprint: lem-sfb-finite-action-compatible-limit)

Explicit universes implement def-weil-size-convention. The compatibility space is
literally a subtype of the product, with its induced topology. The coordinate formula
specifies the action uniquely; continuity below uses this very action.
-/

@[expose] public section

universe u v

/-- Compatible tuples of finite discrete continuous actions form a closed compact
Hausdorff totally disconnected space with a jointly continuous coordinate action.
All projections are continuous and equivariant, without directedness or surjectivity.

Source: Stacks Project, Tags 08ZU, 08ZV, 08ZY, 005C; the product/subspace description
preceding Tag 0A2P; Bhatt–Scholze, Example 4.1.10, p. 28.
(blueprint: lem-sfb-finite-action-compatible-limit)

Proof plan:
1. Each finite stage is compact, including an empty stage. Apply Pi.compactSpace
   (lem-weil-pbc-tychonoff-product-quasi-compact) to obtain compactness of the product.
2. Singleton coordinate cylinders are clopen. Distinct tuples differ in a coordinate,
   so these cylinders separate points and disconnect any subset containing both.
   This proves the Hausdorff and totally disconnected assertions, also for the subtype.
3. A tuple failing compatibility has a cylinder fixing its two offending coordinates
   disjoint from the compatibility locus. Thus that locus is closed.
4. Apply IsClosed.isCompact (lem-weil-pbc-closed-in-quasi-compact) and the equivalence
   between compactness of a subset and compactness of its subtype.
5. Equivariance of r implies that coordinate multiplication preserves compatibility.
   The unit and multiplication laws hold coordinatewise. The same coordinate formula
   says precisely that each projection is equivariant.
6. Projections are continuous by the product/subspace topologies. The i-th coordinate
   of the action factors through (g,z) ↦ (g,z_i) and the jointly continuous stage action.
   The product/subspace topology then gives joint continuity, even for an empty limit. -/
theorem finiteActionCompatibleLimit
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Type v) [PartialOrder I] [Nonempty I]
    (Q : I → Type v) [∀ i : I, Finite (Q i)] [∀ i : I, TopologicalSpace (Q i)]
    [∀ i : I, DiscreteTopology (Q i)] [∀ i : I, MulAction G (Q i)]
    [∀ i : I, ContinuousSMul G (Q i)]
    (r : ∀ (i j : I), i ≤ j → Q j → Q i)
    (r_id : ∀ (i : I) (x : Q i), r i i le_rfl x = x)
    (r_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Q k),
      r i k (le_trans hij hjk) x = r i j hij (r j k hjk x))
    (r_smul : ∀ (i j : I) (hij : i ≤ j) (g : G) (x : Q j),
      r i j hij (g • x) = g • r i j hij x) :
    CompactSpace (∀ i : I, Q i) ∧
    T2Space (∀ i : I, Q i) ∧
    TotallyDisconnectedSpace (∀ i : I, Q i) ∧
    IsClosed {z : ∀ i : I, Q i | ∀ (i j : I) (hij : i ≤ j), r i j hij (z j) = z i} ∧
    CompactSpace {z : ∀ i : I, Q i // ∀ (i j : I) (hij : i ≤ j),
      r i j hij (z j) = z i} ∧
    T2Space {z : ∀ i : I, Q i // ∀ (i j : I) (hij : i ≤ j),
      r i j hij (z j) = z i} ∧
    TotallyDisconnectedSpace {z : ∀ i : I, Q i // ∀ (i j : I) (hij : i ≤ j),
      r i j hij (z j) = z i} ∧
    ∃ a : MulAction G {z : ∀ i : I, Q i // ∀ (i j : I) (hij : i ≤ j),
        r i j hij (z j) = z i},
      Continuous (fun p : G × {z : ∀ i : I, Q i // ∀ (i j : I) (hij : i ≤ j),
        r i j hij (z j) = z i} => a.smul p.1 p.2) ∧
      ∀ i : I,
        Continuous (fun z : {z : ∀ i : I, Q i // ∀ (i j : I) (hij : i ≤ j),
          r i j hij (z j) = z i} => z.val i) ∧
        ∀ (g : G) (z : {z : ∀ i : I, Q i // ∀ (i j : I) (hij : i ≤ j),
            r i j hij (z j) = z i}),
          (a.smul g z).val i = g • z.val i := by
  have _ := r_id
  have _ := r_comp
  let S : Set (∀ i : I, Q i) :=
    {z | ∀ (i j : I) (hij : i ≤ j), r i j hij (z j) = z i}
  have hS : IsClosed S := by
    simp only [S, Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun hij ↦
      isClosed_eq ((continuous_of_discreteTopology (f := r i j hij)).comp
        (continuous_apply j)) (continuous_apply i)
  have hcompact : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  let a : MulAction G S :=
    { smul := fun g z ↦ ⟨fun i ↦ g • z.val i, fun i j hij ↦ by
        change r i j hij (g • z.val j) = g • z.val i
        rw [r_smul, z.property i j hij]⟩
      one_smul := fun z ↦ by
        apply Subtype.ext
        funext i
        exact one_smul G (z.val i)
      mul_smul := fun g h z ↦ by
        apply Subtype.ext
        funext i
        exact mul_smul g h (z.val i) }
  refine ⟨inferInstance, inferInstance, inferInstance, hS, hcompact,
    inferInstance, inferInstance, a, ?_, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_fst.smul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))
  · intro i
    exact ⟨(continuous_apply i).comp continuous_subtype_val, fun _ _ ↦ rfl⟩
