# Stage-1 report: lem-trf-ordered-block-permutation-sign

1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-ordered-block-permutation-sign.json`: item, split into four steps; statement and statement dependencies unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-permutation-sign-ordered-pairs.json`: statement, Mathlib leaf, `Equiv.Perm.sign_eq_prod_prod_Ioi`, `Mathlib/GroupTheory/Perm/Fin.lean:508` (full statement/proof read at 508–511).
- `citations.json`: verbatim statement quotes for every citation in steps 2, 3 and 4. Step 1 has no node citation.
- `searches.jsonl`: actual searches performed by the mandated msearch.py command. Item's prior search records retained; fresh search records added. Leaf searches are exactly the queries in this log.
- `small-cases.json`: exhaustive combinatorial check results, not a compiler test.

2. Attachments

None. The project Lean search by exact blueprint tag and by ordered-block/shuffle/sign notions found no declaration of the whole item. `Fin.signed_face_permutation`, `WeilConjectures/Combinatorics/SignedFacePermutation.lean:36`, treats one deleted index, not the arbitrary two-block assertion. Its statement and proof were read; it is not claimed as an attachment. Mathlib declarations are used as Mathlib leaves, not attachments.

3. Wanted literature

None.

4. What was wrong or missing

The item was statement-only and had no proof. Its statement is correct, including the 1-based index convention. Stacks Tag 07Z7 (`more-algebra.tex`, label `lemma-ideals-generated-by-minors`, lines 1325–1353) only states minor-ideal properties and omits their proof with a determinant expansion hint. It does not assert this numerical sign lemma. The source and proof_origin explicitly distinguish the agent-supplied argument from Stacks' statements.

The latest blueprint ancestor `lem-trf-local-term-locality.proof.md` was read together with the chapter and `sk-i-curve-zero/_section.md`. It concerns contracting correspondences; it has no determinant/Fitting/sign clause. The inherited path through nodal-family geometry and the determinant expansion tool is retained and described honestly in blueprint.from and split_report.blueprint. This is a generic combinatorial calculation below that path, not a replacement for the unit's geometric argument. No unit/chapter record was edited.

The required inherited `coord/dag-sync.md` is absent from this read clone; no synchronization or source files were changed. The explicit live-repository delivery protocol was followed.

5. What remains

No unresolved mathematics. One reusable Mathlib leaf is introduced and there are no new unsplit nodes. Server preflight and delivery results are recorded below after running the required tool.

## Not duplicates

The whole DAG was searched by permutation-sign, shuffle, inversion, ordered-pair, declaration name and Stacks-tag terms. `tools/blueprint_refs.py search` was run for `permutation sign`, `inversion`, `inversions`, `sign_sumCongr`, `sign_eq_prod_prod`, `ordered pairs` and `permutation`. None of the imported blueprint nodes states the ordered-pair product formula. The Mathlib leaf has a direct Mathlib source rather than attributing the formula to an unrelated Stacks tag.

- lem-trf-permutation-sign-ordered-pairs vs lem-trf-ordered-block-permutation-sign: the new leaf gives only the generic pair-product formula for one arbitrary finite permutation; it contains no subsets, shuffles, block restrictions, or subset-sum factor. Steps 1–4 carry those arguments in the item.
- lem-trf-permutation-sign-ordered-pairs vs lem-sfb-shuffle-mixed-corner-cancellation: the existing node treats binary H/V shuffles and cancellation of mixed faces; it gives neither the pair-product formula for arbitrary permutations nor the internal block calculation. Its full statement was read.
- lem-trf-permutation-sign-ordered-pairs vs lem-sfb-shuffle-horizontal-face-reindexing: the existing statement concerns a horizontal-face bijection and its binary-word inversion-count changes. It does not give arbitrary permutation signs. Its full statement was read.
- lem-trf-permutation-sign-ordered-pairs vs lem-sfb-bicosimplicial-shuffle-totalization: the latter constructs a shuffle totalization chain equivalence, using shuffle signs as inputs rather than stating the generic pair-product identity. Its full statement was read.
- lem-trf-permutation-sign-ordered-pairs vs lem-pc-signed-face-permutation: the latter gives the sign compensation for deleting one domain and image position; it does not state the arbitrary pair-product formula. Its full statement and project declaration were read.

The other keyword hits `lem-sfb-cubical-partition-boundary-expansion`, `lem-sp-open-proetale-counit-scalar`, `lem-sfb-symmetric-abel-image-geometry` and `lem-pc-alternating-cech-sorted-contraction` were read and do not state the new leaf: respectively a cubical boundary identity, a coefficient/counit comparison, Abel-image geometry, and a Čech contraction. Parent `lem-trf-minor-laplace-coefficient-formula` was read and is a determinant identity that uses the item, not a sign primitive to cite back (which would be circular).

## Review by Q54

I read the stage-1 brief, worker role, stage contract, GOAL, SETUP's three levels/tool-lemma rules, and both copies of delivery-errors B–E. I reviewed every step against those rules with its cited statements open. The item's source is Stacks Tag 07Z7, at the label and lines specified above. The sole new node's source is the pinned Mathlib `GroupTheory/Perm/Fin.lean:508–511`; I read its complete type, the underlying Iio version at 497–506, and sign's homomorphism definition at `GroupTheory/Perm/Sign.lean:358–405`.

Step 1 uses only the finite sets and bijections in the statement. The concatenated increasing lists exhaust [q] without repetition, so they really define permutations. Bijectivity and sigma(T)=I force sigma(T-complement)=I-complement, giving both induced permutations with precisely the required domains. I evaluated the conjugated middle permutation on both position blocks, fixing the direction of rho and its inverse. This step does not use a sign theorem or an unstated existence lemma.

Step 2 cites only `lem-trf-permutation-sign-ordered-pairs`, whose displayed product is exactly the sign calculation used. For each selected a_j, there are a_j−1 smaller integers and j−1 selected smaller integers; their difference counts the negative cross factors. Increasing order makes all same-block factors positive. This explicitly proves e_A=sum(A)−s(s+1)/2 for both A=T and A=I. The only hypothesis needed by the leaf is that rho_A is a finite permutation, established in step 1. No pre-existing shuffle-sign identity is assumed, and no new node merely restates this part of the item.

Step 3 cites the same leaf for delta, alpha and beta. I checked the cross-factor inequality alpha(j)≤s<s+beta(b) and that shifting second-block indices by s preserves both order comparisons. Thus the three disjoint classes of pairs contribute the two cited products and 1. This derives the block-sign product in place, rather than hiding a new block-factorization lemma or citing a definition for it. The cases of empty pair classes are covered by empty products.

Step 4 cites `def-weil-pbc-matrix-determinant`, whose statement expressly defines sign as a group homomorphism into {±1} and sends transpositions to −1. It therefore gives exactly multiplicativity; the inverse sign is the same sign because both possible values square to 1. The exponents from step 2 differ from the desired exponent by s(s+1), an even integer. These are elementary group and integer identities, explicitly written out. I verified s=0, s=q and q=0 separately; sign(identity)=1 follows from the cited homomorphism, including the empty symmetric group. The verbatim quote in citations.json includes this homomorphism sentence, not an unrelated determinant formula.

For the Mathlib leaf, I checked 0-based Fin m versus the statement's 1-based labels: adding one to both indices and their images preserves precisely the strict comparisons in the product. Coercion from integer units to integers preserves multiplication. The product has no pairs for m=0 or m=1. This is a direct specialization of the cited declaration, not a theorem identifying different mathematical notions. Four real searches (LeanFinder, Loogle, grep, LeanSearch) are logged and copied with unchanged query text. For the item itself I tried two distinct semantic phrasings and read the proposed block-sign, inversion-product and complementary-minor candidates; none states the whole formula in one specialization.

I corrected no false imported statement. The material correction was to supply the omitted argument and make its provenance explicit. I tested the result independently by direct inversion counts on all permutations and all subsets for q=0,...,6: 50,363 permutation/subset pairs, checking both shuffle signs, the middle block sign and the final formula. In particular there is a unique q=0 case, and every s=0 and s=q case is included. All checks passed. Every non-elementary proof step is below 2000 characters (indeed below 700), so no long comparison or separate standard lemma is concealed. No Lean, compiler, Lake, build, repository mutation or agent delegation was used.

## Delivery checks

The required `deliver.py Q54 lem-trf-ordered-block-permutation-sign --no-push` exited successfully: `OK (not pushed) deliver/Q54/lem-trf-ordered-block-permutation-sign at 069c12b05bd: preflight passed`. Local JSON checks also confirmed the statement is unchanged, proof_deps equals the union of step citations, and every quote is verbatim. The actual push command repeats server preflight before publishing the delivery.
