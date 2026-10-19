## Worker report

The module `Sheaf.Topology.NoetherianGoodStratificationRefinement` states
`Topology.exists_finite_good_stratification_refinement`, with its proof exactly `by sorry`.
It introduces no definition. The node is unchanged except for its `lean` record.
The declaration docstring contains all six proof steps, with the original DAG citations.

I read the node, its sole statement dependency, all three additional proof dependencies,
their Mathlib matches, and the corresponding source declarations. I checked Stacks
`literature/stacks-project/topology.tex`, lines 5507–5546 (partition, refinement, goodness,
and the closure-union identity) and lines 5631–5665 (Tag 09Y5 and its proof).
The locally closed input hypothesis is explicit in the node and in Stacks' definition
of partition immediately preceding Tag 09Y5.

Every hypothesis and conclusion is represented as follows:

| Node text | Lean rendering |
| --- | --- |
| A topological space T | `{T : Type u} [TopologicalSpace T]` |
| Closed subsets satisfy DCC | `[TopologicalSpace.NoetherianSpace T]` |
| Finite index set A | `{A : Type v} [Finite A]` |
| The parts P_a are subsets of T | `(P : A → Set T)` |
| Every original part is locally closed | `hP_locallyClosed : ∀ a : A, IsLocallyClosed (P a)` |
| Original parts cover T | `hP_cover : (⋃ a : A, P a) = Set.univ` |
| Original parts are pairwise disjoint | `hP_disjoint : Pairwise (fun a a' : A ↦ Disjoint (P a) (P a'))` |
| A finite family of refined parts | `∃ (n : ℕ) (Q : Fin n → Set T), …` |
| Every refined part is nonempty | `∀ b : Fin n, (Q b).Nonempty` |
| Every refined part is locally closed | `∀ b : Fin n, IsLocallyClosed (Q b)` |
| Refined parts cover T | `(⋃ b : Fin n, Q b) = Set.univ` |
| Refined parts are pairwise disjoint | `Pairwise (fun b c : Fin n ↦ Disjoint (Q b) (Q c))` |
| Each refined part lies in an original part | `∀ b : Fin n, ∃ a : A, Q b ⊆ P a` |
| A part meeting another part's closure lies in it | `∀ b c : Fin n, (Q b ∩ closure (Q c)).Nonempty → Q b ⊆ closure (Q c)` |
| Each closure is a union of parts | `∀ c : Fin n, ∃ I : Set (Fin n), closure (Q c) = ⋃ b ∈ I, Q b` |
| Empty T permits the empty partition | `n : ℕ` has no positivity requirement, so `n = 0` is permitted |

Mathlib's `NoetherianSpace` is defined using ACC on opens. Its equivalence with
`WellFoundedLT (TopologicalSpace.Closeds T)` is clauses 1 and 2 of
`TopologicalSpace.noetherianSpace_TFAE`, read in
`Mathlib/Topology/NoetherianSpace.lean`, lines 51–98. Thus this is exactly the closed-set
DCC hypothesis, not a separation, dimension, scheme, or extra compactness assumption.
The classical DCC/minimal-element equivalence is also explained in the node's first proof
step. The output family can always be indexed by `Fin n` because it is finite; this loses
no possible finite partition. The universes `u` and `v` are explicitly bound and independent.
The input family allows empty parts; no nonemptiness restriction absent from the node is added.
Given covers and pairwise disjointness, containment of each refined part in an original part
is precisely refinement in Stacks' union-of-parts sense.

Dependency interfaces used:

- `def-weil-locally-closed-subset`: `IsLocallyClosed` in
  `Mathlib.Topology.Defs.Basic`, imported through `Mathlib.Topology.LocallyClosed`.
  Its definition is literally an intersection of an open and a closed set; I also read
  `isLocallyClosed_tfae` in `Mathlib.Topology.LocallyClosed` for the equivalent closure form.
- `def-weil-irreducible-components`: `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`, defined by maximality of `IsIrreducible`.
- `lem-sc-irreducible-components-cover`:
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `mem_irreducibleComponent`, and `irreducibleComponent_mem_irreducibleComponents`,
  all in `Mathlib.Topology.Irreducible`.
- `lem-sc-noetherian-finite-irreducible-components`:
  `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` in
  `Mathlib.Topology.NoetherianSpace`.

The statement imports are public. The explicit ordinary import of
`Mathlib.Topology.Irreducible` records the component proof dependencies; the Noetherian
module supplies both the hypothesis and the finite-components theorem. Every recorded
dependency is a Mathlib leaf, so no dependency module or new node is needed.
The existing upstream `Topology.Stratification` is a finite constructible locally closed
partition, with no goodness condition; I read its full structure and
`Topology.Stratification.ofNoetherianSpace`. Neither states this refinement theorem.
The partition properties here are explicit hypotheses and conclusions, not duplicate
definitions of a stratification notion.

Edge cases checked before writing:

- Empty T, including empty A: choose n = 0. Cover is the empty set, which is univ in
  the empty space; every indexed clause is vacuous.
- Nonempty T with empty A: the cover hypothesis is impossible, as required.
- One-point space: the one nonempty input part itself gives the one-stratum refinement.
- Empty input parts or repeated empty parts do not affect the cover or refinement;
  they need not and cannot be retained among the nonempty output parts.
- Finite discrete T: singleton strata refine every partition; closures are singletons.
- Sierpinski T: the two singleton parts are locally closed; the closed-point closure
  is itself and the other point's closure is all of T. Both frontier implications hold.
- No T0 or Hausdorff condition is imposed. In a nonempty indiscrete space, the only
  nonempty locally closed part is the whole space, and the one-part conclusion holds.

Searches made with `msearch.py` (logged in the sandbox's `searches.jsonl`):

- LeanFinder: `Every finite partition of a Noetherian topological space into locally closed
  subsets has a finite good stratification refinement whose closures are unions of strata`.
  Eight hits: `TopologicalSpace.NoetherianSpace.exists_finset_irreducible`,
  `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`,
  `TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`,
  `TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible`,
  `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`,
  `ShrinkingLemma.PartialRefinement`, `exists_clopen_partition_of_clopen_cover`,
  and `ShrinkingLemma.PartialRefinement.exists_gt`. None gives this statement.
- Loogle: `"IsLocallyClosed", "Noetherian"`. Successful search, zero hits.
- Mathlib grep: `goodStratification|good_stratification|stratification.*refin|refin.*stratification`
  in `Topology`. Successful search, zero hits.
- LeanSearch: `A finite locally closed partition of a Noetherian space admits a finite
  refinement satisfying the frontier condition`. Eight hits, including
  `exists_clopen_partition_of_clopen_cover`, `ParacompactSpace.locallyFinite_refinement`,
  `precise_refinement`, `precise_refinement_set`, `frontier`,
  `TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible`,
  `ParacompactSpace.casesOn`, and
  `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`. Their statements concern
  different covers or hypotheses, or only irreducible decomposition; none gives goodness.
- Source and side-library `rg` searches for locally closed partitions, stratification
  refinement, good stratification, and the proposed declaration name found the existing
  upstream `Topology.Stratification`, common refinements, and scheme-specific refinements.
  None gives the arbitrary Noetherian topological good-refinement theorem. Searching the
  item id in upstream source found no declaration. Searching the full proposed name in
  upstream, Mathlib, side-library source, and `dag/lean_names_upstream.json` found no clash.

No statement correction, disputed statement, new node, or unusable dependency was found.
The sole postponed theorem has this item's DAG node and its complete proof docstring.

Validation: file-only compilation with the required `scompile.py` wrapper; dry-run and
delivery results are recorded below after they complete.

Resumption self-check (2026-10-17): retained the saved Lean module and node record.
The current repository comparison changes only `lean`; its signature matches the module
verbatim and every line meets the 100-character limit. Re-read the recorded locally closed
interface, the Noetherian closed-set DCC equivalence, the upstream stratification structure,
and Stacks' partition, goodness and refinement statements. Every hypothesis and conclusion
still agrees with the table above; no repair is needed. The prescribed dry run returned
`OK (dry run): commit 6c1902d5c8 passes the preflight and compiles; nothing pushed`.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
