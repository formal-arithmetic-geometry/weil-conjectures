## Worker report

The module `Sheaf.Topology.InvariantPartitionQuotientSystem` states
`invariantPartition_quotient_system`, with its entire proof postponed by `sorry`.
No definitions, additional nodes, dependency repairs, or statement corrections are needed.
The original node is unchanged except for `lean`.

The finite partition is represented using the dependency's existing
`InvariantDiscreteQuotient G P`, not a second partition definition. Its quotient
values are blocks: the block represented by `B : i.val` is `i.val.proj ⁻¹' {B}`.
`DiscreteQuotient.proj_surjective` makes every such block nonempty;
`DiscreteQuotient.isClopen_preimage` makes it clopen. Fibers are disjoint and cover
P. `DiscreteQuotient.instFiniteQuotientOfCompactSpace` makes the set of blocks
finite. Conversely, the same-block relation of a finite clopen partition is a
discrete quotient. Invariance in the dependency is preservation of that relation
by every group element; applying this also to the inverse shows that blocks are
permuted. Thus the dependency already supplies exactly the node's stated equivalent
index representation.

Hypotheses and clauses, in statement order:

| Node | Lean rendering |
| --- | --- |
| Small representatives and small index | Explicit `universe u v`, `P : Type v`, and `Small.{v} (OrderDual (InvariantDiscreteQuotient G P))`. The index actually lives in `Type v`, independently of the universe of G. |
| Any topological group G | `G : Type u`, `[Group G]`, `[TopologicalSpace G]`, `[IsTopologicalGroup G]`. No compactness, separation, or profiniteness assumption on G. |
| Compact topological P with continuous left action | `P : Type v`, `[TopologicalSpace P]`, `[CompactSpace P]`, `[MulAction G P]`, `[ContinuousSMul G P]`. No Hausdorff or totally disconnected assumption. |
| All finite invariant clopen partitions | The full existing type `InvariantDiscreteQuotient G P`, with the block/fiber interpretation above. No partition or quotient is excluded. |
| i ≤ j means j refines i | `J = OrderDual (InvariantDiscreteQuotient G P)`. Mathlib's underlying quotient order is inclusion of relations, so its dual is exactly the node's convention. |
| J nonempty and directed | `Nonempty J` and `IsDirected J (· ≤ ·)`. |
| J opposite cofiltered | `IsCofiltered Jᵒᵖ`, using J exactly as above. |
| P_i finite and discrete | `∀ i : J, Finite i.val ∧ DiscreteTopology i.val ...`. |
| q_i sends each point to its block, continuously and surjectively | The dependency/Mathlib map `i.val.proj`, with `Continuous i.val.proj` and `Function.Surjective i.val.proj`. |
| r_ji sends a fine block to the unique containing coarse block | For `h : i ≤ j` in J, the canonical `DiscreteQuotient.ofLE h : j.val → i.val`. It maps `[x]` to `[x]`, so is precisely the containing-block map. |
| Every r_ji continuous and surjective | The next universal conjunct asserts `Continuous (DiscreteQuotient.ofLE h)` and `Function.Surjective ...`. |
| r_ii = identity | `DiscreteQuotient.ofLE (le_refl i.val) = id`. |
| r_ki = r_ji composed with r_kj | `DiscreteQuotient.ofLE (le_trans hjk hij) = DiscreteQuotient.ofLE hij ∘ DiscreteQuotient.ofLE hjk`. The proof order here uses Mathlib's fine-to-coarse relation, reversing the displayed J inequalities. |
| r_ji composed with q_j = q_i | `DiscreteQuotient.ofLE h ∘ j.val.proj = i.val.proj`. |
| Left group action on each P_i | `∃ a : ∀ i : J, MulAction G i.val, ...`. These structures contain the group action laws. |
| Joint continuity of every block action | `∀ i, @ContinuousSMul G i.val (a i).toSMul _ _`. The explicit action argument ensures continuity refers to the very action selected by a. |
| Formula g acting on B is its translated subset gB | Equality of fibers: the fiber of `@SMul.smul ... g B` equals `(fun x : P ↦ g • x) '' (i.val.proj ⁻¹' {B})`. |
| All q_i equivariant | `i.val.proj (g • x) = @SMul.smul ... g (i.val.proj x)`. |
| All r_ji equivariant | The next universal equality commutes `DiscreteQuotient.ofLE h` with the two explicit actions `a j` and `a i`. |
| For every nonempty block B, any x_B in B, any C: gB=C iff gx_B belongs to C | The final universally quantified implication has hypothesis `i.val.proj x = B` and conclusion `(@SMul.smul ... g B = C ↔ i.val.proj (g • x) = C)`. Membership in a fiber is exactly the displayed projection equality. All blocks are already nonempty, so this does not introduce an extra nonemptiness restriction. |

Dependency declarations read and used:

- `Sheaf.Topology.InvariantDiscreteQuotient`: full signatures and docstrings of
  `InvariantDiscreteQuotient` and `invariantDiscreteQuotientDiagram` were read.
  The statement uses the former and exactly the latter's object and map formulas
  (`i.val`, `i.val.proj`, `DiscreteQuotient.ofLE`). Import is public.
- `def-weil-size-convention` is explicitly a metatheoretic convention, with no
  declaration/module to import. Explicit universes implement it as its record directs.
- `Mathlib.Topology.DiscreteQuotient`: read the definition, quotient topology,
  projection, canonical refinement maps, identity/composition/projection lemmas,
  finiteness instance, and clopen-fiber statements. These are exposed through the
  existing dependency module.
- `Mathlib.CategoryTheory.Filtered.Basic`: `CategoryTheory.IsCofiltered`, imported
  publicly. Both recorded proof dependencies are also statement dependencies, so
  no additional proof-only import is needed.

Edge cases checked before writing:

- Empty P: there is still a trivial equivalence relation and hence an index.
  Its quotient set is empty, not a singleton fabricated by an index convention.
  All block-indexed conditions, surjectivity, and the point criterion are vacuous;
  both action and projection maps have empty domains where appropriate.
- A singleton or a connected nonempty P: the trivial partition is permitted;
  the theorem never demands a nontrivial finite quotient or point separation.
- Arbitrary noncompact or nondiscrete G: the result uses joint continuity of its
  given action; no finite-orbit refinement or compactness assumption on G is used.
- Non-Hausdorff compact P is allowed. The finite quotient construction needs only
  clopen blocks and compactness, not Hausdorffness or total disconnectedness.
- Equal indices and chains with equality are covered by all universal map formulas.
- Independent universes for G and P: the relation-index subtype and all quotients
  have universe v, without imposing u = v.
- The existential actions are canonical, not arbitrary: their values on every
  quotient projection are prescribed, and projections are surjective. Their
  translated-fiber formula is included explicitly as well.

Searches made (2026-10-24):

- `msearch.py leanfinder`: “Finite invariant clopen partitions of a continuous
  group action form a directed system of finite discrete continuous group sets
  with surjective equivariant maps”. Eight hits included
  `CategoryTheory.PreGaloisCategory.has_decomp_quotients`,
  `exists_clopen_partition_of_clopen_cover`, and direct-limit constructions.
  None states this theorem; the Galois result requires compact G and a given finite action.
- `msearch.py loogle`: `DiscreteQuotient.ofLE, DiscreteQuotient.proj`.
  Four hits included `ofLE_proj`, `ofLE_comp_proj`, `fiber_subset_ofLE`, and
  `exists_of_compat`. These are underlying quotient facts, not the action system.
- `msearch.py grep`: `DiscreteQuotient.*(action|smul)|ContinuousSMul.*DiscreteQuotient`.
  No Mathlib hits.
- `msearch.py leansearch`: “Invariant discrete quotients of a compact continuous
  group action form a cofiltered system of finite continuous actions”. Eight hits,
  including quotient finiteness, `has_decomp_quotients`, and `DiscreteContAction`;
  no exact statement.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for invariant partitions, invariant quotients,
  and the proposed declaration name; `grep -rn` for this node id in
  `lean/WeilConjectures`. Only the dependency, related clopen refinement work,
  and the stronger `profiniteAction_finite_quotients` presentation theorem were
  relevant. The latter requires profinite G and P and is not this statement.
- `rg` over Mathlib and both project source trees for the exact proposed module
  and declaration names found no collisions.

Source read: Bhatt–Scholze, Example 4.1.10 (the provided PDF, converted in the
sandbox), identifying pro-objects in finite discrete G-sets with profinite
continuous G-sets; Stacks `literature/stacks-project/topology.tex`,
`lemma-profinite` (Tag 08ZY), especially its index order and canonical containing-block maps;
also all eight source-carrying proof steps in the assigned node.
No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q38

This is a worker self-check, not a claim of an independent agent review; the brief
assigns independent review to the maintainer and prohibits starting other agents.
I reopened the complete node and module and compared the hypotheses and each
conjunct as in the table above. The order is the dual of the dependency's order,
so J's inequalities and the direction of `ofLE` agree. In particular composition
uses `le_trans hjk hij`, and the category is literally J opposite. The quotient
sets are the existing blocks, not arbitrary finite sets. All existential action
occurrences explicitly use `a i`; the image-of-fiber formula, both equivariance
conditions, and the arbitrary-point criterion are present. No P nonemptiness,
G compactness, Hausdorffness, or total disconnectedness was added. The first
compile exposed the argument order of `ContinuousSMul`; reading its declaration
showed that SMul precedes the topologies, and that explicit application was fixed.
No mathematical statement change was required.
