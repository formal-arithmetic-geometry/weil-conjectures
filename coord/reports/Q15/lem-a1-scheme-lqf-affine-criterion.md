# Worker report

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-scheme-lqf-affine-criterion.json`: four-step split of the existing item; no new nodes and no Mathlib leaves.
- `citations.json`: ten verbatim statement quotations covering every cited node in every step.
- `searches.jsonl`: the authorized Mathlib search-command log, including a second phrasing and LeanSearch.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its blueprint ancestry, and the affine/local quasi-finiteness notions. No sorry-free project declaration states this item exactly. Mathlib's `AlgebraicGeometry.locallyQuasiFinite_iff` was read in `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`; it uses Mathlib's `RingHom.QuasiFinite` and omits the Stacks finite-type/isolated-fibre predicate, so it is not an attachment.

WANTED: none.

## What was wrong and what changed

The imported statement agrees with Stacks Morphisms Tag 01TK and was kept unchanged, including the absence of separation, quasi-compactness, and Noetherian hypotheses. Its proof was empty. I supplied the four implications needed for (1)–(2)–(3)–(1), reusing existing DAG statements rather than creating duplicate nodes. The (1) to (2) step explicitly handles an arbitrary affine pair and an arbitrary prime by passing through the existing finite-type criterion and the isolated-fibre characterization. The affine-open basis is cited wherever affine neighbourhoods or covers are chosen.

No source error or statement correction was found. No part remains unfinished. No Lean was written or compiled.

## Review by Q15

I read the item and its source at Stacks `morphisms.tex`, Lemma 01TK (`lemma-locally-quasi-finite-characterize`), together with the proof of Lemma 01TH and the finite-type criterion 01T2. I also opened every cited DAG statement: `pqf-def-quasifinite`, `lem-weil-pbc-lqf-locally-finite-type`, `lem-weil-pbc-lft-affine-pairs`, `lem-weil-pbc-quasi-finite-at-point-isolated`, `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`, `lem-weil-pbc-affine-opens-basis`, and `lem-weil-pbc-lqf-restriction-to-opens`. Their hypotheses match the uses below.

Step 1 assumes local quasi-finiteness. The finite-type consequence node applies with no extra hypotheses, and the all-affine-pairs node gives finite type for the arbitrary affine pair in condition (2). For each prime I checked that its corresponding point is covered by the definition node, that the locally-finite-type hypothesis required by the point/fibre node has just been supplied, and that the isolated-fibre affine-pair node takes exactly the given affine pair and returns quasi-finiteness at that prime. Thus every clause of (2) is accounted for.

Step 2 uses the affine-open-basis statement twice: first around `f(x)` and then inside the inverse image of that affine. The condition (2) ring map has the finite-type and primewise quasi-finiteness clauses required by `pqf-def-quasifinite`, so it witnesses quasi-finiteness at `x`; no hidden global finiteness assumption is used.

Step 3 constructs an affine cover of the target and affine covers of each inverse image from the same basis statement. The restriction-to-opens node applies because each `A_{ji}` and `B_j` is open and the restricted image condition holds. This gives exactly the local quasi-finiteness required in (3).

Step 4 checks the converse pointwise: the covering hypotheses provide a piece containing any chosen `x`, and the definition's affine witnesses inside that piece remain open subsets of the original schemes. This is the elementary reassembly of the definition and introduces no extra hypothesis.

I checked the empty source, an empty covering piece, an open immersion, and an infinite disjoint union of affine identity maps. The argument allows all of them and never invokes quasi-compactness or separation. The proof has no step over 2000 characters, `proof_deps` is exactly the union of the step uses, and every citation quote is copied verbatim from its node statement. The imported Mathlib searches were reread; the additional LeanSearch query and its result are recorded in `searches.jsonl` and in `mathlib_searches`.
