# Stage-1 worker report: lem-weil-linear-recurrence-shift-span

Group Q43; 2026-10-17. Only this sandbox was written. No Lean was written or compiled, and no delivery was pushed.

## Files written

- `dag/nodes/sec-zeta-weil/lem-weil-linear-recurrence-shift-span.json`: item, split into four proof steps. The mathematical statement is unchanged; the existing definition of span is now cited in it.
- `citations.json`: a verbatim statement quote for each node cited in each proof step.
- `report.md`: this report; `searches.jsonl` is the search command's audit log.

There are 0 new nodes and 0 new Mathlib leaves. The item is not the unit's key node, so no unit record was edited.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, the item id, linear recurrence, shifts, shift spans, and candidate declaration names, and inspected the exact upstream master reference. The closest project declarations are the global `finiteDimensional_shiftSpan_of_forall_add_eq_zero` in `WeilConjectures/ZetaLinearAlgebra/RationalityCriterion.lean:50-75` and `finiteDimensional_shiftSpan_of_recurrence` in `WeilConjectures/ZetaLinearAlgebra/ShiftSpan.lean:107-136`. Their written proofs have no `sorry`, but their conclusions state only finite-dimensionality. The first one's docstring mentions containment and its proof establishes a local `key`; neither the containment nor the explicit dimension bound is an exported declaration conclusion. Thus neither gives every clause of this item and neither is an attachment. A local intermediate proof is not counted as a project declaration.

## WANTED

None. The current blueprint proof and the cited Milne page are available. No missing textbook is used as a proof dependency. Both generic linear-algebra results used below are already Mathlib leaves in the DAG, whose matches were inspected directly.

## Corrections and limits of the imported material

The item's mathematical statement is true and unchanged. Added `def-weil-submodule-span` to its statement dependencies and an explicit citation in the statement for linear span. Its empty proof is replaced by the coordinate calculation, strong induction with base and index inequalities, equality of the two spans and finite generation, and the dimension estimate through an independent subfamily. No new node is needed.

Read the chapter and inherited unit record, then the current `main-20261015` unit and proposition. The current unit gives the two-condition rationality/shift-span formulation; the detailed proposition still includes the recurrence condition and explicitly gives the `(3) => (2)` route of this item. The split follows that route. The ancestor stays `prop-weil-rationality-criterion`, and the item's existing place is retained. The Milne reference motivates the rationality/Hankel dictionary but does not supply this induction; proof origin is correctly `agent`, since the blueprint is agent-written. No unit route is replaced.

The recurrence is applied at `j+s`, not merely `j`: its hypothesis must hold in every coordinate. For induction at `k >= m+d`, the previous indices are `k-d+i`, all nonnegative and strictly smaller than `k` because `k >= d` and `i < d`. The initial exceptional segment is included among the generators. The span definition is by smallest subspace, so step 3 explicitly constructs the subspace of coefficient combinations to justify the finite-spanning interpretation; it does not take a theorem from the span definition that it does not state.

All seeded statement dependencies are retained and needed. Proof dependencies equal the union of step uses. In particular the dimension bound is derived from existing theorem nodes, not merely from the definition of dimension.

## Search audit

Every newly recorded Mathlib search ran through `/home/ubuntu/weil-launcher-nt/msearch.py Q43 lem-weil-linear-recurrence-shift-span ...`, with its exact tool/query in `searches.jsonl`. Searched the item both as an eventual recurrence/initial shift span and as a monic recurrence/translate span. The semantic hits were `LinearRecurrence.IsSolution`, `solSpace`, `solSpace_rank`, `mkSol` and `toInit`; they describe the solution space, not the containment of all translates of an eventually recurrent sequence in its initial shift span. Read `Mathlib/Algebra/LinearRecurrence.lean` and the generic dimension results. The first Loogle query was invalid (`Unknown identifier finrank`); this diagnostic is recorded, not used as evidence of absence, and subsequent valid Loogle searches were run.

Searches for generic dimension bounds also found `finrank_le_of_span_eq_top`, but a separate new node for that bound is unnecessary: `lem-weil-span-independent-subfamily` and `lem-weil-dimension-span-independent-family` already give the estimate in a few lines. These existing Mathlib leaves are cited instead. Inspected `Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean:792-813` (`exists_linearIndependent'` at 799) and `Mathlib/LinearAlgebra/Dimension/Constructions.lean:461-468` (`finrank_span_eq_card`). No search is recorded without having run it.

Searched the whole DAG and the blueprint for finite spans, spanning families, dimension bounds, linear recurrence and shift span, including `tools/blueprint_refs.py ancestor` and `search` for `span dimension at most number generators`, `finite-dimensional shift span`, `span of finitely`, `span of a finite`, `span of the first`, `spanning`, `dimension at most`, and `spanned by`. No blueprint node states the whole item in an equivalent form; its `same_as` is `[]`. The existing span definition and generic linear-algebra leaves are reused. No new Stacks-tagged node or SGA source is involved.

## Not duplicates

No new nodes are delivered. The finite-family independent-subfamily and dimension-of-independent-span results already exist, so the item derives the dimension bound from them rather than creating another generic lemma or a restatement of the item's conclusion.

## Review by Q43

I read delivery-errors B through E in full and audited the actual node statements and sources. For the item I read the current proposition and its proof at `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-prop-criterion/prop-weil-rationality-criterion.proof.md`, especially lines 27-30, plus Milne LEC p. 157 by `pdftotext`. There are no new nodes to review. For the generic tools I read the Mathlib statements and proofs at `LinearIndependent/Lemmas.lean:792-813` and `Dimension/Constructions.lean:461-468`; for every cited definition I opened its DAG statement.

Step 1 cites `def-weil-eventual-linear-recurrence`, whose statement explicitly gives `c_(n+d) = -sum a_i c_(n+i)` for every `n >= m`, and `def-weil-sequence-subspace`, whose statement makes operations coordinatewise. Applied at `n=j+s >= m`, these give the displayed equality of sequences by equality of every coordinate. Nothing is taken from a cited proof or from a docstring-only claim.

Step 2 cites `def-weil-submodule-span` for the smallest subspace containing the initial generators and `def-weil-sequence-subspace` for closure under scalar multiplication and addition. The argument states the strong induction, its generator base case, the identity from step 1, and `0 <= k-d+i < k`. Thus the source's final 'All rows therefore lie...' is proved inside this item, not moved to a new node repeating the goal. The argument is elementary because only the recurrence identity, induction on natural numbers, and closure of a subspace are used.

Step 3 cites the span definition for the two smallest-subspace inclusions and constructs the subspace U of sums over the m+d initial vectors. Its zero, addition and scalar closure are verified by coefficients, using `def-weil-sequence-subspace`. Hence V is exactly this space of combinations. `def-weil-finite-dimensional-subspace` states that such a finite spanning family is finite-dimensionality. This explicitly bridges the intersection definition of span and finite spanning; no missing span-characterization theorem is assumed.

Step 4 cites `lem-weil-span-independent-subfamily`, which states that a finite family has an independent subfamily with the same span, and `lem-weil-dimension-span-independent-family`, which states that the span of k independent vectors has dimension k. Apply the first to the m+d initial rows, relabelling 1-based to 0-based indices; list the resulting subset S in increasing order. The second gives dim V=|S|, while S is a subset of an index set of size m+d, so |S|<=m+d. These are exactly the two cited statements. All hypotheses hold over the given field, and finite-dimensionality was already established in step 3. Neither tool requires the original family independent, distinct, or nonzero.

The edge cases were checked. For m=0,d=1, the recurrence says R_(j+1)=-a_0 R_j, giving a span of one vector; when a_0=0, later shifts vanish. The zero sequence gives V=0. For arbitrary m,d, set all a_i=0 and take only c_(m+d-1)=1. This satisfies the recurrence because it requires c_n=0 only for n>=m+d, and its m+d initial shifts are independent, with distinct last nonzero coordinates. The bound and its indexing are therefore sharp. Repeated or zero rows cause no issue because the extracted subfamily may be smaller; for the zero family it is empty and its span has dimension 0. No division by a recurrence coefficient or characteristic-zero assumption occurs.

B audit: no new node is delivered, every mathematical object is introduced, and the span notion now cites its existing definition. C audit: all cited node statements were opened and verbatim quotes appear in `citations.json`; the only non-elementary operations are the two cited generic linear-algebra facts. D audit: the induction and span identification are proved in the item, with no relabelling of its clauses as new lemmas and no circular use. E audit: all recurrence and induction index hypotheses were verified, and the small cases above checked. No statement dispute or source error was found for this item. Both off-unit statement tools are Mathlib leaves, so no special off-unit tool-use declaration is needed.

## Unfinished work

None in the mathematical split. The mandatory acceptance command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q43 lem-weil-linear-recurrence-shift-span --no-push`; a READY handover is issued only after it prints OK. Final delivery belongs to the independent second reader.

## Second reading by Q43

- Item statement: checked against the current proposition and the source proof's (3)⇒(2) paragraph; hypotheses `m >= 0`, `d >= 1`, the eventual recurrence, all shifts, finite-dimensionality, and the bound `dim_K V <= m+d` agree.
- Step 1: checked against `def-weil-eventual-linear-recurrence` and `def-weil-sequence-subspace`; applying the recurrence at `j+s` and comparing every coordinate gives exactly the displayed shift identity, with `j >= m` explicit.
- Step 2: checked against `def-weil-submodule-span` and `def-weil-sequence-subspace`; the strong induction has the generator base case and the inequalities `0 <= k-d+i < k`, so every later shift is obtained by subspace closure.
- Step 3: checked against the span and subspace statements and `def-weil-finite-dimensional-subspace`; both inclusions `V = W` and the finite coefficient description are written out, including closure of the coefficient set.
- Step 4: checked against `lem-weil-span-independent-subfamily` and `lem-weil-dimension-span-independent-family`; the 1-based/0-based relabelling, empty extracted family, and cardinality bound are valid under `m+d >= 1`.
- New nodes: none; therefore there are no new-node statements or Mathlib leaves to audit. Existing span and linear-algebra nodes were read at their recorded statements and searched for duplicates.
- Edge cases: rechecked the zero sequence, `m=0,d=1` (including `a_0=0`), all-zero coefficients, repeated rows, and an empty independent subfamily; each satisfies the statement and proof.
- Changes: no mathematical file needed repair. Appended this second-reading record; the required dry run passed with `OK (not pushed)` at commit `eb1f41c0a6`.
