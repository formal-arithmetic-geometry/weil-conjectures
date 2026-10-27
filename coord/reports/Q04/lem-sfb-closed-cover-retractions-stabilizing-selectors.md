## Worker report

Item: `lem-sfb-closed-cover-retractions-stabilizing-selectors`, group Q04.
Module: `Sheaf.Topology.ClosedCoverStabilizingSelectors`.
Declaration: `TopologicalSpace.exists_closedCover_retractions_stabilizingSelectors`.
This delivery states the complete existing DAG statement, with one theorem whose
whole proof is `sorry`. It adds no definitions, nodes, hypotheses, or corrected
statements. Only the item's `lean` record changes.

The source is the agent-formulated scalar analytic expansion of the old steps 5–6
below paragraph (3) of the direct-images proof. I read the current file at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`.
The current blueprint itself invokes the open-coefficient preservation result and
does not assert this auxiliary topological theorem. The node already documents
that distinction and the wanted exact literature reference; this delivery
preserves it. The theorem docstring carries all eight accepted proof steps,
including the two Mathlib ingredients, for stage 3.

Hypothesis-by-hypothesis correspondence:

- The space is `S : Type u`, with `universe u` explicitly declared.
  `[MetricSpace S]` supplies the fixed compatible metric and its topology,
  metrization, and Hausdorff separation. Thus a separate `T2Space` hypothesis would
  be redundant. This representation allows every space and compatible metric in
  the node, rather than selecting a special metric or a special type of space.
- `[CompactSpace S]`, `[TotallyDisconnectedSpace S]`, and `[Nonempty S]` are the
  compactness, total disconnectedness, and nonemptiness hypotheses.
- `A : ℕ+ → Set S` indexes precisely the positive integers `j ≥ 1`.
  `hclosed : ∀ j, IsClosed (A j)` and
  `hnonempty : ∀ j, (A j).Nonempty` express closedness and nonemptiness of every
  member. The cover is `hcover : (⋃ j, A j) = Set.univ`.
- The dependency `def-weil-size-convention` is explicitly a metatheoretic
  convention with no declaration or import. Its recorded instruction is to state
  universe hypotheses directly. All sets, finite sets of atoms, and countable
  products here are universe-polymorphic in the same `u`; there is no site or
  derived category requiring a skeleton or a second object universe.

Clause-by-clause correspondence:

1. `∃ P : ℕ+ → Finpartition (Set.univ : Set S)` gives the finite partitions.
   Mathlib's `Finpartition` already requires supremum equal to the whole space,
   supremum independence (pairwise disjointness for sets), and exclusion of the
   bottom set. Consequently its parts are nonempty and cover `S`.
   `∀ i, P (i + 1) ≤ P i` uses Mathlib's order in the refinement direction:
   every later part lies in an earlier part.
2. `∀ i p, p ∈ (P i).parts → IsClopen p ∧
   Metric.diam p < (1 / 2 : ℝ) ^ (i : ℕ)` expresses clopenness and precisely
   diameter `< 2⁻ⁱ`. Every atom is compact, so Mathlib's real-valued diameter
   (which is zero for an unbounded set) has its usual finite meaning here.
3. `∃ ρ : ∀ j, C(S, A j)` gives continuous maps to the actual subspaces `A j`.
   `∀ j (a : A j), ρ j a = a` says that they fix each member of the corresponding
   closed set. Surjectivity follows from this condition, as in the informal
   retraction terminology; it is not an added assumption or extra choice of maps.
4. `∃ e : S → ∀ i : ℕ+, WithDiscreteTopology (P i).parts` gives the product
   of the actual atom types. The existing Mathlib `WithDiscreteTopology` wrapper
   equips each atom type with the discrete topology; the dependent function type
   has its product topology. `∀ s i, s ∈ (e s i).ofTopology.val` uniquely
   characterizes the atom containing `s` by the partition's disjointness and
   covering properties. It does not leave the product map arbitrary.
5. `IsEmbedding e` is Mathlib's assertion of injectivity with induced source
   topology, equivalent to a homeomorphism onto the image.
   `∀ j, (e '' A j).Nonempty ∧ IsClosed (e '' A j)` asserts nonemptiness and
   closedness in the entire product, not merely in `e(S)`.
6. The existentially bound `U : ℕ+ → ℕ+ → Set S` is fixed by the equality
   `U j i = ⋃ (p : (P i).parts) (_ : (p.val ∩ A j).Nonempty), p.val`.
   This is exactly the union of level-`i` atoms meeting `A j`, including
   the specified intersection nonemptiness criterion. No new notion is defined.
7. `∀ j i, IsClopen (U j i)`, `∀ j i, U j (i + 1) ⊆ U j i`, and
   `∀ j, (⋂ i, U j i) = A j` give respectively clopenness, decreasingness,
   and the specified intersection. Successive decreasingness implies the
   corresponding inclusion for arbitrary larger levels.
8. `∃ k : ∀ i : ℕ+, LocallyConstant S {j : ℕ+ // j ≤ i}` supplies exactly
   the maps into `{1, …, i}`, with local constancy bundled in Mathlib's existing
   type. When `∃ j, j ≤ i ∧ s ∈ U j i`, the selected value belongs to
   its own `U` and is at most every eligible `j`. This uniquely specifies
   the least eligible index. When every `j ≤ i` is ineligible, the second
   implication fixes the value to `1`. The two cases exhaust classical logic.
9. `∀ s, ∃ j₀ : ℕ+, s ∈ A j₀ ∧ (∀ j, s ∈ A j → j₀ ≤ j) ∧ …`
   identifies `j₀` as exactly the minimum covering index `j(s)`.
   `∃ i₀ : ℕ+, ∀ i : ℕ+, i₀ ≤ i → (k i s).val = j₀`
   gives pointwise eventual equality. Both `j₀` and the stabilization bound are
   inside `∀ s`, so no uniform stabilization has been introduced. No
   disjointness or openness assumption on the cover appears.

Dependencies and APIs read and used:

- `def-weil-size-convention`: its `lean.convention` record has no module or
  declaration, as discussed above.
- Proof dependency `lem-weil-pbc-profinite-clopen-basis` is the Mathlib leaf
  `isTopologicalBasis_isClopen` in `Mathlib.Topology.Separation.Profinite`.
  I read its full signature, preceding `T2Space`, `CompactSpace`, and
  `TotallyDisconnectedSpace` variables, and the adjacent pointwise lemma
  `compact_exists_isClopen_in_isOpen`. It is imported as a plain proof import.
- Proof dependency `lem-sfb-countable-discrete-product-closed-retraction` is
  `PiNat.exists_retraction_subtype_of_isClosed` in
  `Mathlib.Topology.MetricSpace.PiNat`. I read its full signature and the
  discrete-factor variables. Its conclusion is a subtype retraction fixing
  every subtype element, surjective and continuous, with no finite-factor
  restriction. It is a plain proof import.
- Public statement imports supply the existing notions: positive naturals
  (`Mathlib.Data.PNat.Basic`), finite partitions
  (`Mathlib.Order.Partition.Finpartition`), continuous maps
  (`Mathlib.Topology.ContinuousMap.Basic`), locally constant maps
  (`Mathlib.Topology.LocallyConstant.Basic`), diameter
  (`Mathlib.Topology.MetricSpace.Bounded`), and discrete wrappers
  (`Mathlib.Topology.Order`). No private duplicate of any notion is introduced.

Edge cases checked before writing and during the second pass:

- A singleton space, or any finite discrete space, allows its singleton
  partition at every level, with diameter zero. The positive dyadic bounds
  and the positive-natural indexing include level one without a zero-level
  default-value problem.
- `A j = S` is allowed, as are repeated or overlapping closed sets. Its
  retraction is the identity, its neighbourhood unions equal `S`, and the
  least-index rule still has its stated meaning.
- At a level before the first covering index, there may be no eligible
  index. The rule explicitly defaults to `1`, an element of every positive
  interval `{1, …, i}`. Later eligibility does not constrain these earlier
  values incorrectly.
- The first covering index may be `1`; minimality has no smaller positive
  index to exclude, and the stabilization assertion handles that case.
- A convergent sequence with its limit is a compact metrizable totally
  disconnected example with a singleton closed cover. Its first-index
  function need not be continuous or uniformly stabilized; the statement
  requires only each finite selector to be locally constant and the bound
  to depend on the point.
- Empty `S` and empty `A j` are precisely excluded by the original hypotheses.
  No completeness, separability, disjointness, or openness binder was added.

Searches for an existing declaration (all using the read-only source trees or
the prescribed `msearch.py` wrapper):

- `leanfinder`: “A countable closed cover of a compact metric totally
  disconnected space admits finite refining clopen partitions and continuous
  retractions with locally constant selectors eventually equal to the least
  covering index”. Eight hits: finite clopen partitions/approximations and
  `Profinite.NobelingProof.fin_comap_jointlySurjective`; none states this theorem.
- `loogle`: `PiNat.exists_retraction_subtype_of_isClosed`. One exact hit for
  the existing proof-dependency leaf, not for the combined statement.
- `msearch.py grep`: `ClopenPartition|clopenPartition|stabiliz.*select|select.*stabiliz`
  in Mathlib `Topology`: zero hits.
- `leansearch`: “A compact metric totally disconnected space with a countable
  nonempty closed cover has continuous retractions and locally constant selectors
  eventually equal to the least covering index”. Eight hits concern clopen
  covers, the PiNat retraction, compact exhaustions, and topology instances;
  none gives the combined theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for closed covers,
  clopen partitions, and stabilizing selectors found scheme-specific closed-cover
  results and the finite clopen-cover cohomology argument, with no duplicate.
  `grep -rn` for this node id in `lean/WeilConjectures` found no attachment.
- An exact-name search for `ClosedCoverStabilizingSelectors`,
  `exists_closedCover_retractions_stabilizingSelectors`, `stabilizingSelectors`,
  and `stabilizing_selectors` in Mathlib, both project roots, and
  `dag/lean_names_upstream.json` found no existing declaration.
- Read Mathlib's `Finpartition` structure, refinement order, diameter definition,
  `LocallyConstant`, `WithTopology`, and `WithDiscreteTopology` rather than
  inventing helper structures or canonical maps.

No new nodes, dependency repairs, statement correction, or statement dispute.

Validation: `scompile.py Q04 lem-sfb-closed-cover-retractions-stabilizing-selectors`
on this delivered file succeeded in both sandbox and library module modes
(1.8 seconds each), without errors or warnings. All variables and the sole
universe parameter are explicitly bound. There is exactly one postponed theorem.

## Second reading by Q04

I reread the node and the completed file clause by clause in a separate pass.
This is a self-check, not a claim of an independent reviewer: the dispatcher
explicitly prohibits starting other agents, and the maintainer supplies the
independent delivery review.

The metric binder includes precisely the compatible fixed metric and Hausdorff
topology; compactness, total disconnectedness, nonemptiness, and all closed-cover
hypotheses are present. I checked Mathlib's refinement-order definition so the
successor inequality is in the correct direction. The partitions cover the whole
space and exclude empty atoms through `Finpartition`. Diameter uses the positive
index, not an off-by-one natural index. The atom map's coordinate is required to
contain its point, so disjointness determines it uniquely. The discrete wrapper
and product topology are the specified ones. `IsEmbedding` is exactly the
homeomorphism-onto-image clause, while closedness is asserted in the ambient
product. The retractions target the actual `A j` and fix every subtype point.

The union equation includes exactly those atoms meeting `A j`. Clopenness,
decreasingness, and intersection are all present. The selector codomain forces
positivity and the upper bound, and both its least-eligible and no-eligible
branches are stated, with default value one. The final minimum is characterized
by both membership and minimality; the eventual bound lies under the point
quantifier. The statement does not silently require uniformity or closed-cover
disjointness or openness. No mismatch was found and no statement changed during
this pass. I also reread the eight-step proof docstring against the accepted
node proof and checked the explicit universe and binders.
