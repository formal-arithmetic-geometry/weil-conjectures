# Q120: lem-trf-quotient-pair-tensor-kernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-quotient-pair-tensor-kernel.json`: statement, split into four proof steps; unchanged statement and statement dependencies; no exact Mathlib match for the complete item.
- `citations.json`: six verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: actual Mathlib search records produced by msearch.py, retained together with all inherited searches in the item.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The split uses existing Mathlib leaves `lem-weil-pbc-tensor-finite-product` and `lem-weil-pbc-tensor-right-exact`.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, quotient-pair names and tensor/kernel terminology. No project declaration states all the coordinate, exactness and restricted-image clauses. Sorry declarations and Mathlib declarations were not treated as attachments.

## WANTED

None. All necessary literature is present.

## What was wrong or missing

The item had no proof, and recorded searches alone did not resolve it. Its statement is correct; no statement dispute or correction is needed. The source's assertion that tensor commutes with the pushout is expanded using the exact presentation rather than assuming tensor preserves an initial injection. The full item is not a Mathlib leaf: tensor-kernel comparisons returned by search assume flatness or describe another map, and the restricted-image identity still requires its coordinate argument. The inherited metadata, ancestry, source and unit are retained.

Read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`, its proof and `_section.md`, and the chapter/unit records. This auxiliary algebra node belongs to the existing descent chain serving that ancestor; it neither replaces the geometric proof nor changes the unit route.

## Not duplicates

No new nodes were created. Whole-DAG searches for the tag, quotient-pair and tensor/kernel terminology and blueprint_refs searches for tensor right exactness, tensor direct sums, quotient/tensor kernels and tensor finite products were read. Existing finite-product tensor distribution and tensor right exactness are reused. The parent pushout-domination lemma and tensor-kernel-factorization cite this item, so neither can serve as a proof dependency. No dependency points back to a citer.

## Review by Q120

I read Stacks `algebra.tex`, Tag 0AUM (`lemma-domination-universally-injective`, especially the quotient description and the tensor-kernel short exact sequence at lines 20936 onward), Tag 00DF (`lemma-tensor-product-exact`, lines 1994 onward), and Tag 00CX (`lemma-tensor-product`, lines 1716 onward). The tag/label pairs 0AUM and 00DF agree with `tags/tags`. No SGA source is used. There are no new nodes requiring separate sources or searches.

For Step 1 I opened and read all three cited statements. The direct-sum definition gives componentwise operations and finite support; for two coordinates every pair has finite support, so it is the ordinary product. `lem-weil-pbc-tensor-finite-product` explicitly supplies the isomorphism with the pure-tensor formula for these two factors. The tensor definition supplies induced linear maps and generation by pure tensors. The displayed inverse is checked on the generating pairs, and the other composite is checked on a pure tensor using additivity in its first entry. Thus no unsupported distribution or identification is hidden. Step 1 is marked non-elementary because it invokes the finite-product tensor lemma. Mathlib's `TensorProduct.prodLeft` and `prodLeft_tmul` (Prod.lean:63,69) confirm this ingredient; the existing leaf records the general finite-product version `TensorProduct.piLeft` (Pi.lean:115), whose source I also read.

Step 2 cites the full tensor definition, which states both pure-tensor generation and functoriality for composition. Evaluating the first identity at x tensor l yields (b(x) tensor l,-a(x) tensor l); linearity extends it to every w. The second identity is exactly pi_L composed with the tensor inclusion, so functoriality gives j_L. This is elementary and does not use a theorem about preserving kernels.

In Step 3 I read the full statement of `lem-weil-pbc-tensor-right-exact`: it explicitly assumes surjectivity of the second map and equality of its kernel with the first map's image, and concludes both right-tensored exactness and terminal surjectivity. These are exactly the two given hypotheses on pi. Substitution (M1,M2,M3,N)=(P,D,E,L) uses arbitrary modules over the same commutative ring. No flatness or injectivity is required. I read `rTensor_exact` in RightExactness.lean:401 as a further check. The substantive right-exactness theorem is a cited existing Mathlib leaf, not hidden in prose or a fresh node.

Step 4 reuses that same right-exactness statement under the already verified hypotheses. Starting with s in ker j_L, it lifts G(s,0) through delta_L. Applying the established inverse F gives both b_L(w)=s and a_L(w)=0, including the minus sign in the second coordinate. Conversely a_L(w)=0 gives delta_L(w)=G(b_L(w),0), and pi_L delta_L=0 proves j_L(b_L(w))=0. These are elementary substitutions in the previously established formulas, with both inclusions explicit. The image is b_L(ker a_L), not the tensor of ker a.

Small-case checks: L=0 gives zero source and target everywhere. For P=0, pi is an isomorphism, so j_L has zero kernel; the formula has zero image. If a=0, projection of im delta_L is im b_L and the formula gives exactly that image. If b=0 it gives zero kernel for the first leg. If a is the identity its tensor remains the identity, and the kernel again vanishes. The zero ring makes every module zero. For R=Z, P=Q=Q'=Z, a=2, b=id and pi(y,z)=2y+z onto E=Z, one has ker pi={(x,-2x)} and j=2. With L=Z/2, a_L=j_L=0 and b_L=id, so both sides of the kernel formula are Z/2 even though ker a=0. This non-flat example checks the exact issue that could otherwise invalidate the argument.

Against delivery-errors B--E: no fresh elementary, duplicate or clause-restating nodes; all notions are already defined by the two unchanged statement dependencies; TeX is singly escaped in the JSON values; each cited node's statement was read and copied verbatim into citations.json; the six quotes were checked as substrings. There is no appeal to a cited node's proof. Every non-elementary fact is one of the two existing Mathlib leaves. The construction, formulas and final kernel inclusions are written in the item's proof. No step exceeds 2000 characters (lengths 789, 373, 432, 710); none hides an independent comparison lemma. All four search kinds were actually run through msearch.py, a second semantic phrasing was tried, and the candidate source types were read. Flat kernel isomorphisms do not apply to arbitrary L, algebra tensor kernel lemmas concern algebra homomorphisms, and map_ker concerns the tensor product of two quotient maps; none is a one-line specialization proving the full item. No source error, statement weakening, change of coefficients or route departure was needed.

## Unfinished work

None in this one-level split. Validation and push are performed by deliver.py after this report is written; the maintainer performs the independent review.
