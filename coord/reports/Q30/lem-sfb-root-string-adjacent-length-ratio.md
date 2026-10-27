## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-root-string-adjacent-length-ratio.json`: item, statement unchanged, five-step split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-root-string-length-bound.json`: statement, Mathlib leaf, `RootPairing.chainBotCoeff_add_chainTopCoeff_le_three`, `Mathlib/LinearAlgebra/RootSystem/Chain.lean:475–482`.
- `citations.json`: every step/node citation, with the verbatim statement supplying it.

Attachments: none. The search of `lean/WeilConjectures/` for the exact blueprint id and for `root.string`, `RootPairing`, `chainBotCoeff`, and `chainTopCoeff` returned no declaration. No Lean was written and no compiler or Lake command was run.

WANTED: none. Milne's Algebraic Groups (2017) is available locally.

The original item was unsplit, not false. Its identity is an agent-formulated consequence of the rank-two diagrams; Milne does not state this exact adjacent-root formula as a named theorem. I retained its statement and gave an explicit algebraic verification using the existing endpoint-difference and integer-interval leaves and one new length-bound leaf. The formula for an invariant form is derived in the proof instead of hidden behind a reference. Positive definiteness is applied only to the three nonzero roots already present. There is no irreducibility, root-spanning or finite-dimensionality hypothesis added.

Nothing remains unfinished. The sandbox was initially empty of node files and report; no previous split or searches were overwritten. The imported item searches were retained, and new actual searches are recorded in `searches.jsonl` and the relevant nodes.

## Blueprint and searches

I read the chapter/unit records and the newest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The existing dependency chain places this calculation under the Chevalley normalization prerequisite on the alteration branch of the open-direct-image input. No unit or chapter route is changed. `python3 tools/blueprint_refs.py ancestor lem-sfb-root-string-adjacent-length-ratio` returns `None`; both item and new leaf retain this null nearest ancestor and the existing via chain, extended by the item for the new leaf. Their `from.place` explicitly describes the supporting calculation; `same_as=[]` records the blueprint searches.

Whole-blueprint searches for `root string`, `root-string`, `root system`, `string`, `crystallographic`, and `chainBotCoeff` found no corresponding blueprint statement. Searching the whole DAG's statements for the root-string notions found the integer-interval and endpoint-difference leaves, which I reused. A whole-DAG search for the bound declaration found other nodes' search results, not a statement of this general bound. Searches of statement text for strings with a bound, and of the Mathlib declaration name, ruled out a duplicate general length-bound node. The Lie-algebra string-central-parity node includes a bound in a much more specialized Lie-algebra setting and assumes Chevalley basis data absent here.

All new leaf searches were executed with the required `msearch.py Q30 lem-sfb-root-string-adjacent-length-ratio` wrapper: LeanFinder for the endpoint-sum bound; Loogle with `RootPairing.chainBotCoeff, RootPairing.chainTopCoeff`; grep for the exact bound declaration in `LinearAlgebra/RootSystem`; LeanSearch for the four-root length bound. These identify the exact leaf. I read Chain.lean's hypotheses at 35–41, endpoint conventions at 110–164 and 186–192, endpoint-difference statement/proof at 405–422, and bound statement/proof at 475–482. The item was searched with two additional full-formula LeanFinder phrasings. Their hits are special embedded-G2 lengths, form evaluation identities, or a different coefficient product using five indices, not the whole adjacent-root identity. No unavailable service is reported as a negative match; no unexecuted query was added.

## Not duplicates

lem-sfb-root-string-length-bound vs lem-sfb-root-string-integer-interval: the new leaf bounds the sum of the endpoints by three and needs reducedness; the existing leaf identifies the entire interval of integer roots and has no reducedness assumption.

lem-sfb-root-string-length-bound vs lem-sfb-root-string-endpoint-difference: the new leaf bounds the endpoint sum; the existing leaf identifies their difference with the Cartan integer and has no reducedness assumption.

lem-sfb-root-string-length-bound vs lem-sfb-chevalley-string-central-parity: the new leaf concerns arbitrary finite reduced rational root pairings without Lie-algebra data; the existing statement requires a split semisimple Lie algebra and Chevalley basis, selects an ordering, and gives divided adjoint powers and central commutators. It cannot be applied under this item's hypotheses.

lem-sfb-root-string-length-bound vs lem-sfb-root-string-adjacent-length-ratio: the new leaf contains no bilinear form, no adjacent-root norm identity and no sum root; it supplies the independent endpoint bound used in the item's explicit calculation. It is not a clause of the item or a replacement proof of it.

## Review by Q30

I read Milne Appendix C.19–C.20, printed p.611 (PDF p.623), and Section g, printed pp.621–622 (PDF pp.633–634), including table (180) and all four rank-two diagrams. The source uses an invariant inner product and integral coroot evaluations. The item's rational formulation is handled entirely by rational bilinear algebra; no real scalar extension or classification comparison is assumed. The new leaf is precisely Mathlib's reduced crystallographic endpoint bound specialized to Q; its source is also visible in those four diagrams. Its statement introduces every object and endpoint convention inline, names the field definition, contains no proof, and has empty proof lists. Its Mathlib declaration/file/line and scoped hypotheses were checked directly.

Step 1 is the direct two-line expansion of reflection invariance with the second argument the reflected root. The sign is crucial: `s_l(a_l)=-a_l`, so invariance gives `b(x,a_l)=-b(x,a_l)+c b(a_l,a_l)`. This proves the coroot/form formula for every x without invoking an unlisted theorem. Root-coroot value 2 ensures all three roots are nonzero, and the given positivity gives A,B,D>0.

Step 2 cites the statements, not the proofs, of `lem-sfb-root-string-endpoint-difference`, `lem-sfb-root-string-integer-interval`, and the new bound. I opened each node. The first explicitly states p-q equals the second root on the first coroot, so its orientation is exactly the t used here. The second explicitly gives the integer interval and can be applied at z=1 because gamma=alpha+beta is the given root; hence q>=1. The new leaf explicitly supplies p+q<=3. All have finite index and rational crystallographic hypotheses already given, and only the bound needs reducedness, which the item has. Their statements are quoted verbatim in `citations.json`. Enumerating six pairs from these natural-number inequalities is elementary.

Step 3 uses t=-1 in D=B+(t+1)A and q=p+1. Step 4 uses an integer r supplied by the crystallographic hypothesis, not an extra integrality theorem. Positivity of D yields B>(q-1)A; for q=2 or 3 this forces -2<r<0, so r=-1. Step 5 uses the coroot of the given sum root k: uD=(p+1)A, with u an integer and 0<u<2 because p=1 or 2 and B>0. Thus u=1. These are short substitutions and integer inequalities from step 1 and the hypotheses. No independent comparison, identification or standard lemma is hidden in them. Every non-elementary input occurs as a node citation in step 2, and `proof_deps` is exactly that union. No step exceeds 2000 characters.

For edge cases I checked that empty or rank-one systems admit no independent pair and that A1×A1 admits no sum root, so the item is vacuous there; the new bound still applies to its independent pairs with p=q=0. I also enumerated all independent ordered pairs with a sum root in the exact integral-coordinate diagrams: A2 (12 pairs), B2 (24), G2 (60), with Gram matrices (2,-1,2), (2,-2,4), (2,-3,6) respectively. Every endpoint and squared-norm identity passed, covering all six (p,q) cases; `small-cases.txt` records these checks. The G2 cases (0,3), (1,2), and (2,1) in particular check the endpoint orientation and the unequal-length coefficients. The rational bilinear argument remains valid for reducible ambient systems and additional directions outside the root span.

The B–E review found no statement error to repair. It did lead me to reuse the existing interval and difference leaves, and to replace a possible rank-two classification black box by the explicit integer calculations in steps 3–5. Only the general Mathlib length bound is new. All writes are within the designated sandbox; no SGA source is cited. The independent server `review_split` check passed before report packaging.
