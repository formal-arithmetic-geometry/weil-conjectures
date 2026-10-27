# Stage-1 report: lem-trf-tail-factorizations-tensor-kernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tail-factorizations-tensor-kernel.json`: statement; split into four steps, reusing existing Mathlib leaves; no Mathlib match for the whole item.
- `citations.json`: four entries, one for each cited node in each proof step, checked as verbatim substrings of the live statements.
- `report.md`: this report. Search command results are retained in `searches.jsonl`.

No new nodes and no new Mathlib leaves. The two theorem inputs already exist as Mathlib leaves: `lem-weil-pbc-tensor-commutes-with-colimits` and `lem-weil-pbc-filtered-colimit-modules-elementwise`.

## Attachments

None. Searched the project library under `lean/WeilConjectures/` for the blueprint tag, tail/factorization terminology, tensor kernels and direct-limit kernels. No project declaration states this item. Existing tensor-tower results concern inverse limits and different hypotheses, and do not attach. No Lean was written or compiled.

## WANTED

None. All needed sources are in the supplied Stacks checkout.

## What changed and what was wrong

The imported statement is correct and unchanged. Its proof was empty. The proof now expands Tag 059E's kernel-union argument into tensor-colimit preservation, eventual zero detection, advancement to a common upper bound, and application of the assumed tail factorization. The last two are elementary steps, not new lemmas. In particular, no finite presentation or Mittag-Leffler hypothesis is imported from the surrounding proposition: those hypotheses are unused in this direction of its proof.

Retained the item's source, statement dependencies, blueprint ancestry and prior search records. Appended only actual Q34 searches, with the exact tool/query and actual logged result. A second semantic phrasing found tensor-kernel/right-exactness results rather than the tail bound; those do not give the item in one line. Read the concrete hits `TensorProduct.directLimitLeft` and its leg-compatibility lemmas (`Mathlib/LinearAlgebra/TensorProduct/DirectLimit.lean:78,82,86,90`) and `Module.DirectLimit.of.zero_exact` (`Mathlib/Algebra/Colimit/Module.lean:272`). These support the existing leaves, rather than making the whole item a leaf.

Read the latest blueprint ancestor `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof, and the unit's latest `_section.md`, together with the DAG chapter and unit records. This is an inherited algebra support item beneath the local-projectivity/descent chain, not a restatement of any ancestor clause. The ancestor command confirmed `lem-trf-local-term-locality`. Whole-DAG concept searches located the two existing leaves and the tensor-product definition. Whole-blueprint searches for `tensor`, `tensor colimit`, `059E`, and `tensor products commute with colimits` found no equivalent blueprint statement of the item. `same_as` remains empty. The chapter and unit route are unchanged; the generic Mathlib leaves are tools under the project rules.

## Unfinished work

None for this stage-1 split. The pre-existing Mathlib leaves are cited without modifying them. No new unsplit obligations are introduced.

## Not duplicates

No new nodes were created. In particular, the tensor-colimit comparison and eventual-zero assertions reuse existing nodes instead of creating special cases.

## Review by Q34

I read `literature/stacks-project/algebra.tex`, Tag 059E (`proposition-ML-characterization`), specifically the proof that (3) implies (2). Its claim that the kernel into the tensor colimit is the union of stage kernels is precisely the non-elementary content needed here. I checked its two ingredients in Tag 00DD (`lemma-tensor-products-commute-with-limits`, including the specified coprojection maps) and Tags 00D6/00D7 (`lemma-directed-colimit`, `lemma-zero-directed-limit`). No SGA source is used. There are no new nodes needing separate source reviews.

For step 1 I opened the statement of `lem-weil-pbc-tensor-commutes-with-colimits`. It asserts a colimit with apex M tensor N and with legs exactly mu_i tensor 1, for any small diagram with a given module colimit. Thus it identifies the actual cocone of this item, not merely an abstractly isomorphic module. Here R is commutative, I is small, and the module L is arbitrary, so all hypotheses hold.

For step 2 I opened `lem-weil-pbc-filtered-colimit-modules-elementwise`. Its explicit in-particular clause states that zero under a coprojection is equivalent to zero under some later transition. The small nonempty directed poset is filtered, and step 1 has supplied the required colimit of tensor modules. The node places no finite-presentation condition on its modules. Therefore the witness k_0 is available for any tensor z in the asserted kernel, not just a pure tensor or a finitely generated input.

For steps 3 and 4 I opened `def-weil-pbc-module-tensor-product`. Its statement explicitly includes induced maps, linearity, and compatibility with composition and identities. Step 3 writes out the composition through k_0 and uses that a linear map sends zero to zero. Directedness gives k above both k_0 and j. Step 4 applies the given h_k only at this k, tensors its specified equality, and evaluates it at z. These are short consequences of a cited statement and the item's own hypotheses; neither hides a new theorem. No compatibility between the different h_k is needed: only one is chosen for each z.

I tested the degenerate cases: with a singleton index or i=j, the factorization hypothesis forces the needed retraction identity, so the proof still yields tensor injectivity; when L=0 or M_i=0 the inclusion is immediate and the steps remain valid; the zero ring gives only zero unital modules. A finite diagram with a greatest element has its zero witness there; for a general directed poset a witness k_0 incomparable with j is handled by the explicit common-upper-bound step. This is why tail-only factorizations suffice. I verified that no flatness, countability, finite-generation or finite-presentation assumption appears in the proof.

Against delivery-errors B through E: no new node is elementary, duplicated, or a renamed clause because none is created; every non-elementary input is a cited statement that explicitly says what is used; all four citation quotes match those statements verbatim; proof_deps is exactly the union of uses; statement dependencies still define the two named notions; the proof does not use an existing node's proof or introduce a cycle through an ancestor. All steps are under 500 characters, so none meets the long-step threshold. No statement correction or source error was needed.
