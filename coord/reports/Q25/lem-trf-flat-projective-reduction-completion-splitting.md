# Delivery report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-flat-projective-reduction-completion-splitting.json`: statement node, now split into seven steps; no exact Mathlib match under the item's arbitrary-ring and arbitrary-module hypotheses.
- `citations.json`: verbatim statement quotations for every node cited by every proof step.
- `searches.jsonl`: actual search-command log, retained across the draft and repair.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searching the project declarations in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag and for the completion/projective-reduction notion found no declaration proving the whole item without sorry. The read-only upstream master is not treated as evidence of a finished proof.

WANTED: none.

## Statement and route audit

The imported statement agrees with Stacks Tag 05D3, `lemma-split-completed-sequence`, in `literature/stacks-project/algebra.tex`: the source's middle module P is called E here; its flat last module and projective reduction hypotheses, arbitrary ideal and ring, and split exact completion conclusion are all preserved. There is no statement dispute. No Noetherian, finite generation, completeness or separation hypothesis is added.

The current blueprint's trace-formula locality ancestor is not a new occurrence of this commutative-algebra statement. This item entered through the historical supporting chain from Tag 05DP to Tag 05DK to Tag 05D3. I retained its inherited chapter, unit and ancestor chain and made the precise place explicit; no blueprint statement with the same conclusion was found. The proof follows the Stacks supporting route and reuses existing nodes, rather than changing the trace-formula route.

The first draft used a flat Tor criterion without citing a tensor exactness statement, and incorrectly inferred that two representatives with the same image modulo I^nM differ in I^nE. I corrected these before this delivery: Step 1 cites the precise existing tensor exactness theorem and quotient identification; Step 4 corrects the discrepancy in M by a finite sum of lifted elements and never makes the invalid inference in E. I also removed the proposed completion-exactness node: it restated one clause of the item, and Step 7 now proves that clause directly from the quotient maps. An omitted argument in the Stacks proof is not a source error: its surjectivity and compatibility checks are expanded here.

## Review by Q25

I read the full statement and proof of Tag 05D3, the imported item, its blueprint ancestry, and the full statements of all five cited existing DAG nodes. There are no new nodes requiring an additional source review. I checked the delivery-errors B–E requirements against the resulting proof, especially that each citation actually states the fact used and that no non-elementary input is left uncited.

Step 1 uses `lem-weil-pbc-flat-quotient-tensor-injective`, whose statement gives the entire tensor short exact sequence when the last term is flat. Its hypotheses are precisely the given short exact sequence and the given flatness of M, with N = R/I^n. Clause (1) of `lem-weil-pbc-tensor-over-quotient-ring` supplies the actual quotient tensor isomorphisms. Its displayed formula identifies the maps with the maps induced by u and v and verifies their transition compatibility; this does not rely on an unstated Tor long exact sequence.

Step 2 uses `lem-weil-pbc-flat-module-quotient-flat` with J = I^n. It states exactly flatness of M/I^nM over R/I^n. The ideal J_n in R/I^n is nilpotent with exponent n, including n = 1; quotienting by its action gives the original projective reduction M/IM. The explicit representative maps check the ring and module identifications. The lifting characterization in `def-weil-pbc-projective-module` transports projectivity across those isomorphisms. Thus every hypothesis of `lem-trf-local-nilpotent-projective-flat-lift` is verified, and that node's conclusion is exactly projectivity of M_n over A_n. None of these statements imposes a finiteness condition.

Step 3 invokes the projective definition's final equivalence, that maps from a projective module lift along every surjection, with the identity of M_1 and the quotient surjection v_1. It then defines P as an inverse image submodule. Step 4 is the elementary finite-sum argument left out in the source: choosing e_0 above s_n([m]) only shows m-v(e_0) lies in I^nM. Writing that difference as a finite ideal sum and lifting each factor through the original surjection gives p in P with v(p) = m. This proves the required quotient surjection without presuming anything about e-e_0 in E. The induced map is well-defined because linearity sends I^{n+1}P into I^{n+1}M.

Step 5 again uses the precise lifting property of `def-weil-pbc-projective-module`, now over A_{n+1}. The canonical map j is justified by containment of the corresponding ideal multiples, and its composite with v_{n+1} is pi. I checked compatibility separately from the section identity: for a representative p of t(y), applying v_n to the equation [p] = s_n(w) forces w to be the reduction of y. Therefore the chosen section really extends the previous section; arbitrary unrelated quotient splittings would not suffice.

Step 6 is componentwise assembly of this compatible family and proves both linearity and the right-inverse identity. Step 7 uses the quotient short exact sequences already proved in Step 1. Existence and uniqueness of each k_n follows from their middle exactness and injectivity; applying u_n to the two possible transitions proves compatibility of k_n by injectivity. This verifies injectivity and middle exactness of the completion maps directly. These final steps use only equalities of explicitly defined compatible families and do not hide a general inverse-limit-exactness theorem.

For small cases I checked I = 0, where quotient sequences are constant and the hypothesis makes M projective; I = R, where all quotient modules and completions are zero; M = 0; K = 0; and n = 1 in the nilpotent lift, where J_1 = 0. Every construction still makes sense. I reviewed each step for hidden non-elementary claims; all are shorter than 2000 characters, and the only explicit comparisons are quotient maps with their kernels and the componentwise compatibility calculation written out above. No elementary step or clause of the item was made a new node.

All new searches were run using the prescribed msearch command; the inherited searches and real log entries are retained. The valid directory grep found `AdicCompletion.map_exact` at `Mathlib/RingTheory/AdicCompletion/Exactness.lean:184`; reading its context shows the Noetherian and finite middle-module restrictions. It gives no linear splitting from projective reduction. `map_surjective` gives only one clause. The natural-language searches also returned compatible element lifts and generic projectivity lemmas, not the item. The malformed Loogle query and the grep with a redundant Mathlib directory prefix are expressly marked inconclusive, and were followed by a valid comma-separated Loogle query and the corrected directory grep. No Mathlib absence claim rests on those unsuccessful queries.

## Unfinished work

None within this one-level split. The existing nilpotent-projectivity node remains an independent DAG input; no claim is made to have formalized it. No Lean was written and no compiler, Lake or build tool was run.
