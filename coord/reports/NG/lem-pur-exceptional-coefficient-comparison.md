# Stage-1 report: lem-pur-exceptional-coefficient-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-exceptional-coefficient-comparison.json`: statement, now split into ten steps. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim cited statement for each step/node pair.
- `searches.jsonl`: actual results logged by msearch.py; the item retains its inherited searches and appends the six searches run here.

The two Python files in this sandbox only write/refine this item's JSON and citations. They are not project changes or delivery files.

## Attachments

None. I searched the project source by the exact blueprint tag and exceptional/coefficient notions, and inspected the ordinary-etale UpperShriek, TensorHom and IntegralCoefficients files. No project declaration states all the clauses of this item. In particular, `nonempty_iso_map_reductionModIdeal` has a nonzerodivisor hypothesis and concerns cone reduction; it does not state the specified coefficient comparisons for non-flat maps between finite quotient rings. General Mathlib mate naturality/pasting exists, but is already represented by `def-weil-pbc-adjunction-mate` and `lem-weil-pbc-mate-pasting` and does not make this whole item an attachment or Mathlib leaf.

## WANTED

None. The proof is marked agent-written because the blueprint is agent-written and the mixed base-change calculation is expanded here.

## What was wrong or missing

The item had no proof. Its hypotheses and conclusions are retained. I clarified the existing ordinary-etale meanings of bounded constructible and finite Tor amplitude inline and added their notion dependencies; this does not import the finite-field or pro-etale definition as the meaning of the statement. No statement dispute or mathematical counterexample was found.

The sparse blueprint tensor paragraph says projection commutes with coefficients without expanding the comparison. Step 6 now applies the existing ringed projection/exchange identity to the coefficient square, and step 7 writes both exceptional transposes. The additional geometric base-change clause needs the mixed proper square (step 8), its open/proper composite (step 9), and the exceptional transpose calculation (step 10).

Blueprint ancestry is preserved: `tools/blueprint_refs.py ancestor` reports a null blueprint ancestor, through the existing via list ending in the seeded target. The item realizes the counit compatibility in unit sk-thm-purity-transport Step 1, and (2) plus the tensor portion of (3) of the current sk-lem-sp-reduction-compatibilities proof. Searches for counit-transpose and tensor coherence returned no equivalent blueprint node. The more general keyword search and statements read found related nodes, but all have different scheme/coefficient domains or additional conclusions: notably det-sp-reduction-compatibilities and lem-pur-finite-coefficient-adjoint-comparisons concern the fixed-field pro-etale setting and cannot be cited as this ordinary-etale arbitrary-Noetherian item. No chapter or unit route changed.

## What remains unfinished

Nothing in this one-level split. Existing prerequisite nodes remain separate obligations of the DAG. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes were created. All non-elementary inputs reuse existing nodes. Elementary local-free tensor observations and explicit counit calculations stay in the item's steps.

## Review by NG

I read coord/brief-stage1.md, the complete B–E delivery-error checklist, the chapter and unit records, the three route levels in SETUP.md, GOAL.md and coord/dag-sync.md. The sandbox initially contained only dispatcher markers: no interrupted split, searches, report or delivery result existed, and no delivery command for this item was active. I retained the imported item's proof provenance, prior searches and blueprint ancestry. This is direct delivery by the dispatched worker; it is not an independent second-reader review.

For the item I read the current sk-lem-sp-reduction proof and all three paragraphs of sk-lem-sp-reduction-compatibilities.proof.md. I also read the archived thm-asd-smooth-tensor statement and proof, and the local Stacks source: 0GL6 remark-Rf-lower-shriek-change-of-rings, 0E48 remark-compatible-with-diagram, and the construction of compact-support base change in 0F7L lemma-base-change-shriek. These give the specified proper/open normalization. The ringed formal calculations use 07A4 tensor/pullback and 07A7 base-change mates; generic pasting is the existing node backed by Mathlib Mates.lean. No SGA source is used, and no oriented purity theorem or the parent finite-smooth coefficient theorem is used to prove this item's comparisons.

For steps 1–3 I opened the actual statements, rather than their dependency lists. The origin-equivalence node really gives bounded constructible etale/pro-etale comparison for arbitrary finite rings; det-pe-finite-tor-comparison-noetherian transfers the Tor interval for a qcqs scheme and a discrete Noetherian ring. Here A is a finite Noetherian ring and the schemes are Noetherian, hence qcqs. Thus the finite-reduction lemma applies to the specified origin, supplies a bounded flat model and puts scalar reductions back in the ordinary-etale constructible finite-Tor category. The smooth tensor theorem really applies over a Noetherian base with the integer N=ell^r invertible, and gives both the rank-one object and the canonical tensor isomorphism on the entire ordinary-etale derived category. The pullback-K-flat node gives flat terms as well as K-flatness; the bounded-flat criterion gives the explicit interval [a-2d,b-2d]. The constructible-set pullback statement allows arbitrary scheme morphisms. I added the finite-affine-cover node so that the disjoint union of trivializing neighborhoods is qcqs; the constructibility-descent node expressly requires a surjective map of qcqs schemes and finite coefficients. It applies to each cohomology sheaf there. Tensoring with a rank-one locally free sheaf is locally the identity, a short argument from its definition, not a new lemma node.

For steps 4–5 I checked the adjunction/mate statements and the direction of every inverse. The source is P_B S_X G_A K, so the transpose uses b^{-1}, not b. The construction is pointwise under the ambient adjunction: no unsupported adjunction on a restricted subcategory is needed. Naturality follows by comparing the displayed transposes. In step 5 the middle b^{-1} is moved past P_C S(c) by naturality, then the B-counit identity is substituted; the final equality uses exactly the assumed b cocycle. The mate-pasting node states this vertical-pasting law. I do not assume an invertible left square has an invertible right mate.

For steps 6–7 I read the ringed projection/exchange node: it allows an arbitrary commutative square of ringed topoi, not just a geometric Cartesian square. This is why it applies to the identity underlying topoi with coefficient map A to B, even when the map is non-flat. Its proper exchange is the coefficient map of the item because both are defined as the transpose of the same scalar-extended proper counit. The proper projection node specifies the signed symmetry normalization with K first. The open-derived-tensor node states the unbounded canonical tensor identity and its sheaf/K-flat construction. Hence composing those identities compares the actual compact-support projection maps. Step 7 writes the transposes of both requested tensor composites, substitutes the defining identity for c at A_Y, and uses that projection identity. It does not use orientation compatibility, which would be a stronger and different obligation.

For steps 8–10 I verified that the cited mate-pasting statement gives the transpose of a pasted proper square. Both paths in step 8 transpose to S h^* of the A-proper counit. Their pullback identifications are the same balancing map on flat K-flat models. This is an explicit short application of the existing generic pasting theorem, rather than an unproved assertion that comparisons transport. In step 9 the open equality holds for the underived sheaf comparisons before deriving; I corrected the wording to avoid suggesting equality of arbitrary derived maps can be detected by stalks. The compact-support-comparison node expressly normalizes E_R as proper exchange followed by the open comparison on a pulled-back compactification, and states its independence of compactification. This justifies using step 9 for the specified maps. The smooth exceptional base-change node specifies beta by the inverse E_R followed by the pulled-back counit. Step 10 writes both transposes under P'_B adjoint G'_B; the inverse of step 9 equates them. No inverse of c is taken. Both Y' and X' have the required Noetherian and smooth hypotheses, and compactifiability is required in the item.

I tested the statements and calculations at r=m (identity coefficient comparison), r=m=n (identity cocycle), f=id, d=0, the empty scheme, K=0, identity geometric base change, and a genuinely non-flat quotient such as Z/ell^2 to Z/ell. The proof uses flat models over the source ring; it never treats the quotient as flat. The shift convention is checked: L[2d] places cohomology in degree -2d. The rank-one twist can be nontrivial, since only etale trivializations are used. No global trivialization or chosen orientation is introduced.

Against B–E: there are no new statement-only nodes to audit for duplication, elementary padding, or relocation of an item's clause. All cited statements were opened and are copied verbatim into citations.json (30 step/node pairs). No source tag substitutes for a missing citation. The record's proof_deps is the exact union of uses. Generic off-unit tools have individual reasons in split_report.tool_uses, and the coefficient-counit route stays intact. I checked that the main proposed dependencies do not reach this item. Every proof step is under 2000 characters (maximum 1295), and the substantive comparison calculations have their generic ringed/mate inputs cited. No theorem's internal proof is used as though it were its statement. The existing source item is not weakened and none of its conclusions is dropped.

The preliminary server review_split check passed before the final cover/projection citation refinements. The required final deliver.py dry run and push results are recorded by the delivery tool.
