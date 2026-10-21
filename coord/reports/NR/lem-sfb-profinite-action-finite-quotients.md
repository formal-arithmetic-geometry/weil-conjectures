## Worker report

The item states `profiniteAction_finite_quotients` in
`Sheaf.Topology.ProfiniteActionFiniteQuotients`, with one postponed proof (`sorry`).
Its natural-language statement is unchanged. NN's merged delivery at 19:01 UTC on
2026-10-21 was a stage-1 split, with no Lean attachment; this delivery supplies
stage 2, without resplitting or redelivering that split. The sandbox had only brief
markers before this work. No shared source or launcher script was edited.

Hypothesis and conclusion correspondence:

- The size convention is metatheoretic: its recorded `lean.convention` explicitly
  has no declaration or module. `universe u v`, `G : Type u`, `P : Type v`, and
  `I : Type v` implement its small-representative convention. The invariant index
  is a subtype of `DiscreteQuotient P : Type v`; its diagram takes values in
  `TopCat.{v}`. No category of all types or larger unbounded index is used.
- The profinite group is `[Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]`. Its specified open-normal
  neighbourhood basis is exactly `hG : ∀ U ∈ 𝓝 (1 : G), ∃ N :
  OpenNormalSubgroup G, (N : Set G) ⊆ U`. In particular this is not replaced by
  an arbitrary topological group or by an unmentioned choice of an action.
- In the forward half, `P` carries `[TopologicalSpace P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] [MulAction G P]
  [ContinuousSMul G P]`. The last class means joint continuity on `G × P`.
- `DiscreteQuotient P` represents the finite clopen partitions: its equivalence
  classes are open and closed, pairwise disjoint, nonempty, and cover `P`.
  Mathlib's compactness instance makes the quotient finite. This represents the
  empty partition of the empty space as well. It adds no enumeration or labels.
- `InvariantDiscreteQuotient G P` requires preservation of the equivalence
  relation by every `g`. Applying this also to `g⁻¹` means that blocks are
  permuted, not necessarily fixed. It does not restrict to orbit partitions.
- `∀ s, ∃ i, i.val ≤ s` says every finite clopen partition has an invariant
  refinement. Mathlib orders relations by inclusion: finer partitions are
  smaller. Consequently `IsCofiltered (InvariantDiscreteQuotient G P)` states
  the small cofiltered indexing assertion directly (including nonemptiness).
  This reverses the numerical order convention in the proof, not the diagram:
  arrows still go from fine partitions to coarse partitions.
- `invariantDiscreteQuotientDiagram` is the actual functor whose objects are
  quotient sets with their discrete quotient topology and whose maps are
  `DiscreteQuotient.ofLE`. Functor laws are supplied by Mathlib's existing
  `ofLE_refl_apply` and `ofLE_ofLE`, not by postponed existence claims.
- The explicit `Finite i.val ∧ DiscreteTopology i.val ∧
  Function.Surjective i.val.proj` records the finite discrete stages and
  surjective quotient projections. Continuity of these projections is already
  Mathlib's `DiscreteQuotient.proj_continuous`. The next conjunct gives
  surjectivity of every transition `DiscreteQuotient.ofLE h`.
- The existential family `a` gives an action on each stage. Its `ContinuousSMul`
  clause and the equation `i.val.proj (g • p) = g • i.val.proj p` identify these
  as the canonical continuous quotient actions; surjectivity of the projections
  determines their values on every quotient point. The following equation makes
  every containing-block transition equivariant. These are not arbitrary actions.
- `TopCat.limitCone (invariantDiscreteQuotientDiagram G P)` is Mathlib's explicit
  compatible-family limit: the subtype of the dependent product satisfying
  every transition equation. Its topology is the subtype of the product
  topology, not a topology chosen by the theorem.
- The action `b` on that limit is characterized by
  `(g • z).val i = @SMul.smul G i.val (a i).toSMul g (z.val i)`;
  this is exactly the coordinatewise action and determines it uniquely.
  `ContinuousSMul` asserts its joint continuity.
- The homeomorphism `e` has the required canonical value on every coordinate:
  `(e p).val i = i.val.proj p`. The last forward equation
  `e (g • p) = g • e p` gives equivariance. The coordinate equation fixes the
  map itself, not just its isomorphism class.
- The converse quantifies over every `I : Type v` with `[PartialOrder I]
  [Nonempty I] [IsDirected I (· ≤ ·)]`. `F : Iᵒᵖ ⥤ TopCat.{v}` is precisely an
  inverse system, including identity and composition laws. Its stage assumptions
  are `[∀ i, Finite (F.obj i)] [∀ i, DiscreteTopology (F.obj i)]
  [∀ i, MulAction G (F.obj i)] [∀ i, ContinuousSMul G (F.obj i)]`.
  The implication premise is equivariance of every transition. Continuous maps
  are already built into `TopCat` morphisms. No transition is assumed surjective.
- The converse conclusion asserts `CompactSpace`, `T2Space`, and
  `TotallyDisconnectedSpace` for the same concrete `TopCat.limitCone F`.
  Its existential action is fixed coordinatewise by the final equation, and
  its joint continuity is `ContinuousSMul`. No stage or limit is required
  nonempty.

Dependency interfaces read and used:

- `def-weil-size-convention`: its `lean` is a convention record, not a missing
  declaration; no dependency repair or dummy import is appropriate.
- New node `def-sfb-invariant-discrete-quotients`:
  `Sheaf.Topology.InvariantDiscreteQuotient`, declarations
  `InvariantDiscreteQuotient` and `invariantDiscreteQuotientDiagram`.
- Mathlib `Mathlib.Topology.DiscreteQuotient`: `DiscreteQuotient`, `proj`,
  `proj_surjective`, `proj_continuous`, `isClopen_setOfPred_rel`, its finite and
  discrete-topology instances, `ofLE`, `ofLE_continuous`, `ofLE_refl_apply`,
  `ofLE_ofLE`. Read the definitions and their surrounding API, including the
  relation-inclusion orientation of refinement.
- `Mathlib.Topology.Category.TopCat.Limits.Basic`, `TopCat.limitCone`: read the
  full compatible-family subtype, its subspace/product topology and projections.
- Proof-only imports for the recorded proof dependencies:
  `Mathlib.Topology.Homeomorph.Lemmas`,
  `isHomeomorph_iff_continuous_bijective`;
  `Mathlib.Topology.Separation.Profinite`, `isTopologicalBasis_isClopen`;
  `Mathlib.Topology.Compactness.Compact`, `Pi.compactSpace`.
  Each recorded signature and source place was read. The theorem docstring
  retains the complete ten-step proof and names these DAG dependencies.

Edge cases checked before writing: empty `P` has the unique empty quotient,
with no chosen block or point; its quotient limit has an empty coordinate and
is empty. A singleton or a trivial group needs no nontriviality assumption.
For a connected compact action image, invariance permits permutations rather
than fixing blocks. In the converse, empty stages force an empty product and
limit, for which compactness, Hausdorffness and total disconnectedness all hold.
Non-surjective equivariant transition maps are allowed. A one-element indexing
poset gives the finite stage itself. No discrete or trivial action assumption
has been imposed on the profinite input.

Searches for the item: msearch LeanFinder query “A continuous action of a
profinite group on a profinite space is the inverse limit of its finite
equivariant clopen quotients” returned profinite-group quotient limits and
fundamental-group continuity, not arbitrary actions. Loogle
`DiscreteQuotient, ContinuousSMul` returned no hits. Mathlib grep
`invariant.*[Dd]iscreteQuotient|[Dd]iscreteQuotient.*invariant|[Pp]rofinite.*[Aa]ction|[Aa]ction.*[Pp]rofinite`
returned no hits. `rg` in both project roots found finite Galois actions and
`exists_finite_invariant_clopen_partition`; its full signature concerns Galois
scheme base change, not arbitrary compact group actions on profinite spaces.
The item's blueprint ID has no upstream declaration. Ordinary `Profinite.asLimit`
and `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor` do not state
this equivariant partition result. No exact existing statement was found.

Source validation: read Bhatt–Scholze Example 4.1.10 on PDF p. 28 and the
clopen-partition proof of Stacks `topology.tex`, lemma-profinite (Tag 08ZY).
No statement correction, disputed clause or dependency interface repair.

## New nodes

`def-sfb-invariant-discrete-quotients` defines the small subtype of Mathlib
clopen discrete quotients preserved by the group action, with its inherited
refinement order and canonical topological quotient diagram. Its source is
Bhatt–Scholze Example 4.1.10, p. 28 and the invariant version of Stacks 08ZY.
It is cited in the item's `stmt_deps`. The module contains real subtype and
functor data; the latter uses only already proved Mathlib functor-law equations.
It contains no `sorry`, choice from an existence theorem, or auxiliary axiom.
The subsequent theorem supplies cofilteredness, quotient continuity and the
limit identification; those properties are not assumed in the definition.

Before creating it, msearch LeanSearch query “The clopen discrete quotients of
a topological space whose equivalence relation is invariant under a group
action” found underlying `DiscreteQuotient` and orbit relations only; the
former is reused and the latter is not an invariant partition. Loogle
`DiscreteQuotient, MulAction` and Mathlib grep for invariant discrete quotients
and the two proposed declaration names returned no hits. Project searches in
both `WeilConjectures` and `Sheaf` likewise found no matching definition.
DAG searches found only the assigned theorem, its field-site consumer, and
unrelated scheme/logarithmic/categorical quotients. `blueprint_refs.py search
'invariant discrete quotient'` returned zero matches, and its `ancestor`
command returned `None`, as the inherited creation chain records. The new
node preserves that null imported ancestor and extends the item's `via` route.
Raw msearch result records are included in its `mathlib_searches`.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
