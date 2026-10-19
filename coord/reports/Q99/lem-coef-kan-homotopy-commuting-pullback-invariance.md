# Q99 stage-1 delivery

Item: lem-coef-kan-homotopy-commuting-pullback-invariance.

## Files written

- dag/nodes/sec-six-functors/lem-coef-kan-homotopy-commuting-pullback-invariance.json: existing statement, now split into seven steps; no exact Mathlib match.
- citations.json: one verbatim statement excerpt for each of the fourteen step citations.
- searches.jsonl: actual search-command records, retained with their results summarized in the item.
- report.md: this report.

No new nodes and no new Mathlib leaves. The sandbox also contains item-source.json (the unchanged source node) and write_split.py (the initial writing helper); these are scratch material, not delivery files. The delivered JSON, not the helper's initial version, includes the subsequent corrections described below.

## Attachments

None. I searched the entire read-only WeilConjectures source under /home/ubuntu/weil-src-slopmaster2 for the blueprint id and for homotopy/pullback terminology. No declaration states this item; master sorry declarations were not treated as completed proofs. This item has no recorded closed Lean audit.

## Wanted literature

WANTED: archival Kerodon, Construction 3.4.0.3 (010B), Proposition 3.4.0.9 (032B), Proposition 3.4.0.2 (0109), Corollary 3.1.3.3 (00TM), Definition 3.1.7.12 (00UA), Corollary 3.6.4.3 (03X7), and Subsection 4.6.8 (01PF), for lem-coef-kan-homotopy-commuting-pullback-invariance. These were read online; no document was downloaded. These are Kerodon identifiers, not Stacks tags. The endpoint-adjustment proof is agent-written, not attributed as a literal theorem of 032B.

## What needed correction

The local shared checkout initially lacked the assigned node. A read-only server read found the actual unsplit node, which I preserved as item-source.json; after the normal shared refresh the local file was identical. No invented replacement item or maintainer metadata was written.

The source explicitly warns that 032B assumes strict commutation. It cannot by itself justify the homotopy-commuting comparison. The split now performs the missing operation: lift the pair of endpoint homotopies through the endpoint path fibration, then prove that this lift induces a weak equivalence. All choices and higher parameters are handled by relative pushout-products. The formula's inverse denotes coherent path inversion, not precomposition by an order-reversing map of Delta^1 (which would not be simplicial).

The original statement's doubled TeX backslashes were normalized; no hypothesis, conclusion, or coefficient category was changed. While reviewing my draft I corrected a notation error: a general path on Q_0 need not be c(gamma), so step 6 now calls it eta and substitutes c(gamma) only after precomposition with q. I also replaced a vague reference to varying parameters by the explicit total family Q_M, its subcomplex Q_K, and the precise relative extension domain. Neither correction changes the proposition.

## Not duplicates

No new node was created. DAG and whole-blueprint searches for homotopy pullbacks and endpoint homotopies led to reuse of lem-coef-kan-homotopy-pullback-invariance and lem-coef-kan-pullback-fibration-invariance. The former requires strict commutation, so it does not subsume this item. The broader lem-coef-infinity-kan-homotopy-coherent-cube-invariance has an additional square and cube assertion, so using it would merely shift this item's substance upward. The endpoint-adjustment argument is written here instead.

## Mathlib searches

The sandbox records two LeanFinder phrasings, one LeanSearch query, Loogle, and grep. I read the returned types and the relevant source in ModelCategory/PathObject.lean and ModelCategory/RightHomotopy.lean, especially RightHomotopy.weakEquivalence_iff (lines 143-149). These give abstract path objects, right homotopies, composition of path objects and weak-equivalence cancellation. They do not state the explicit map between simplicial path-model pullbacks under the two given endpoint homotopies, or its relative coherent parameter construction. The grep for homotopyPullback, homotopy_pullback and RightHomotopy.trans_h returned no hits in the pinned source. I did not promote a candidate to a Mathlib leaf without the missing identifications.

## Review by Q99

I read the chapter and unit records, the ancestor blueprint prop-coef-integral-exceptional-adjoint (paragraph 2, derived coefficient adjunction), and the entire item source. The unit has no numbered proof steps; this is a foundational tool below its recorded derived-adjunction branch, not a change to the biduality route. I read Kerodon 010B and 032B for the path model and strict comparison, 0109 for arbitrary-base fibration pullbacks, 00TM for endpoint restriction, 00UA with 03X7 for the testing convention, and 01PF for coherent rather than strict path composition. There is no appeal to SGA. There are no new nodes whose independent statements or sources need auditing.

For step 1 I opened lem-coef-kan-homotopy-pullback-invariance and checked its statement includes exactly the strict-span map used twice here. The first vertical triple is (identity,c,identity); the last is (a,identity,b). All six vertices in each application are Kan complexes. None of the original noncommuting faces is called strict: the intermediate spans have been defined to make these particular faces strict.

For step 2 I opened def-cbc-enhanced-diagrams-cones and lem-coef-sset-anodyne-pushout-product, and read the latter's Mathlib source at AnodyneExtensions/PushoutProduct.lean:95-103 and the lifting definition at Basic.lean:71-75. Its statement permits any monomorphism and any map with the stated lifting property. A horn has that property by the definition of Kan fibration. Transposing the endpoint horn square therefore gives exactly its pushout-product, and the pullback fibration claim is proved by projecting and pairing a filler. This is a direct application of the cited statement, not an uncited model-category theorem.

For step 3 I opened lem-cbc-realization-weak-equivalence and checked that it allows arbitrary source and target simplicial sets. The monotone min/max maps supply the two explicit contraction homotopies, and precomposition turns them into inverse testing functions. I opened lem-coef-kan-pullback-fibration-invariance: it assumes neither the base nor the total object is Kan. With both left legs p and with vertical maps (identity,identity,j_i), every hypothesis is satisfied, and the induced map is exactly J_i. Using a lemma restricted to Kan bases here would have been incorrect because X times Delta^1 need not be Kan.

For step 4 the same pushout-product statement supplies the lift with initial value J_0, since the endpoint inclusion is a dimension-one horn. The lower map is explicitly (r(z),t), so its last endpoint lands in Q_1 and preserves x,y. The adjunction with Fun(Delta^1,W') supplies the full square, including all higher simplices; no pointwise selection is being mistaken for a simplicial map.

For step 5 I used the full testing criterion from lem-cbc-realization-weak-equivalence, not a claim about only pi_0 of the underlying spaces. The lift homotopy identifies the precomposition functions for every Kan target; cancellation of bijections then proves tau weak. The last strict comparison is again exactly the statement of lem-coef-kan-homotopy-pullback-invariance. Composition is checked by composing these testing bijections.

For step 6 I checked the horn indices and orientations: Lambda_1^2 prescribes A to B_0 to B', while Lambda_0^2 prescribes A to A' and A to B'. The missing edge is A' to B', which is precisely the desired output direction. Each whole-parameter horn inclusion is an instance of the cited pushout-product statement. The two glued triangles form the same square used in step 4; no independent associativity or strict path-reversal lemma is assumed. This explains the original coherent concatenation notation by actual simplicial triangles.

For step 7 I checked the relative domain against the statement of lem-coef-sset-anodyne-pushout-product. It is the pushout-product of Q_0 times K into Q_0 times M with the initial endpoint horn. At a boundary of dimension one it joins two chosen lifts and, after endpoint restriction, joins their comparison maps over X. Higher boundaries give compatible higher comparisons by the identical stated lifting property. For varying data, Q_K into Q_M is a monomorphism of total simplicial sets; no unjustified trivialization of a family is used. The two triangle-filling restrictions have the same relative lifting property with the corresponding horn, so coherent triangle choices are also covered.

I checked small cases: empty U or V makes the initial path object empty and every construction remains defined; if W is empty, existence of u,v forces U,V empty, and the given weak equivalences force the corresponding primed emptiness. Discrete Kan complexes admit only constant homotopies, so the construction reduces to the strict comparison. With W' a point the endpoint lift is uniquely determined on path coordinates. Nontrivial loops in W' can change the comparison when H_u or H_v changes; the proof only asserts independence of fillers for fixed specified homotopies, and it transports further homotopies of those data rather than erasing them. I checked there is no dependency path back to this item from any of the four statement tools. All steps have fewer than 2000 characters; the longest is the explicit relative parameter lifting calculation. The two off-unit foundational tools are declared in split_report.tool_uses.

The C4 citation audit used the actual statements of all five cited nodes; citations.json copies their wording verbatim. No proof of a cited node is used as an extra interface. B1-B9 cause no new-node issue; the only edited DAG file is the assigned item. All non-elementary imported facts have node citations; the elementary steps give their horn/pushout-product arguments explicitly rather than naming an unproved transport theorem.

## Unfinished work

No mathematical part of the split remains. The referenced nodes keep their own existing state; this delivery does not assert new Lean proofs. Required server checks and direct delivery follow this report.
