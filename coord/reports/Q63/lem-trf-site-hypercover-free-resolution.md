1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-site-hypercover-free-resolution.json`: repaired item, seven proof steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-cech-nerve-one-coskeletal.json`: new statement-only generic lemma, unsplit; no Mathlib match for ordinary 1-coskeletality. Mathlib's Cech adjunction supplies the augmentation-map clause but not the whole statement.
- `citations.json`: eleven verbatim statement quotations, one for each node/step citation.

2. Attachments: none. Read-only searches of the entire project's WeilConjectures source for the item tag, hypercover exactness/resolutions and coskeleta yielded no exact project declaration. The CechComplex construction concerns indexed Cech complexes, not this arbitrary-site all-degree hypercover theorem.

3. WANTED: none. The sources used are present in the shared literature.

4. What was wrong and repaired: the returned delivery at head `88f7a2b3fe` identified the ordinary zero-coskeleton with a relative Cech nerve. That identification is false. The source does not make it: Stacks 01GE defines its degree-zero stage separately. The repair retains the coskeleton route, defines that relative nerve explicitly, and treats the first transition separately using its 1-coskeletality. It also spells out why the slice matching objects agree with ordinary presheaf matching objects only in dimensions at least two, and why the cover hypotheses imply the exact sheaf-surjectivity condition of the comparison lemma. The initial required dry run of the retained delivery passed mechanically; its success did not resolve the mathematical return.

5. What could not be finished: no mathematical part of the stage-1 split remains. The new generic lemma is intentionally statement-only, as required for a one-level split.

## Repair of E3/C4

Take the constant simplicial set K on W={0,1}, augmented by the identity to W. Then the ordinary zero-coskeleton has q-simplices W^(q+1), whereas the relative nerve of K_0 -> W has only two q-simplices for every q. In degree one they have respectively four and two elements. Their free abelian zeroth homology groups have ranks one and two. Thus replacing the relative nerve by the ordinary zero-coskeleton destroys precisely the desired degree-zero identification.

Step 2 now defines K^0 as the fibre-product nerve over G=h_W. Step 4 uses the separate new lemma, extracted from Stacks 018I, to prove that this nerve is 1-coskeletal and receive the canonical map from K^1. Its degree-one map is explicitly the pair of endpoint maps into K_0 x_G K_0, so the n=1 matching hypothesis applies without replacing that fibre product by an ordinary product. Only n>=2 uses the ordinary matching/coskeleton identification. This is a correction of the returned proof, not a dispute of the item's true statement or of Stacks 01GE.

## Repair of A4: attribution and historical ancestry

The split and this repair are by Q63 on item `lem-trf-site-hypercover-free-resolution`; the item's `split_report.worker` is now `Q63`, its `split_report.item` is this item, and every new node's `created.item` and `created.group` are this item and Q63. The report and delivery are likewise Q63's.

The existing item's historical `created` record is identical in the returned sandbox and current shared repository: it was created by Q37 while splitting `lem-trf-site-hypercover-injective-sections`. That field records creation, not the worker who subsequently splits the node. The standing brief says to keep historical fields, and preflight check 9 forbids changing this maintainer-owned field. The delivery tool's `merge_split_node` explicitly keeps it from the authoritative base even if a sandbox changes it. Moreover changing its `created.item` to itself would break its blueprint ancestry by creating a self-loop in the creator chain. Accordingly I corrected the split/repair attribution in the fields owned by this delivery and retained the correct historical creator and parent. This ownership distinction is made explicit for the maintainer's review of the A4 return; no false claim of creating the existing node is made.

## Searches retained and added

Read the retained `searches.jsonl` before searching. The original four item searches are retained unchanged in the item. Added a second semantic phrasing of the item. For `lem-trf-cech-nerve-one-coskeletal`, ran LeanFinder twice with distinct phrasings, LeanSearch, Loogle with both Cech/cosk and IsCoskeletal/Cech patterns, and two grep queries through msearch.py. Each node record reproduces the actual tool and query and retains the search log result, including its returned declaration names. No unavailable service is reported as a negative result.

Read Mathlib/AlgebraicTopology/CechNerve.lean lines 45-180: Arrow.cechNerve, SimplicialObject.cechNerveEquiv and cechNerveAdjunction construct the nerve and the augmentation map. Read SimplicialObject/Coskeletal.lean lines 50-105: the generic class and isCoskeletal_iff_isIso characterize coskeletality, but no instance there establishes 1-coskeletality of this nerve. The second LeanFinder result Nerve.cosk₂Iso concerns 2-coskeletality of an ordinary category nerve, not the stated 1-coskeletality. Hence the new node is unsplit, with the useful partial Mathlib result recorded in the search verdicts.

Whole-DAG keyword/tag searches and blueprint_refs searches for Cech nerve, coskeleton, coskeletal, 018I, and hypercover found no existing generic statement with this content. The arbitrary-site item is more general than the blueprint's split etale hypercover node; the latter does not replace it.

## Not duplicates

lem-trf-cech-nerve-one-coskeletal vs lem-weil-pbc-cech-nerve-free-homology: the new node gives the relative nerve's ordinary 1-coskeletality and the universal vertex-tuple map; the existing node computes free-sheaf homology under local surjectivity. The new node assumes no local surjectivity and asserts no homology calculation.
lem-trf-cech-nerve-one-coskeletal vs lem-weil-pbc-set-cech-nerve-free-resolution: the new node concerns presheaf coskeletality and maps from simplicial presheaves; the existing node is the free-module resolution of the set-level nerve of a surjection.
lem-trf-cech-nerve-one-coskeletal vs lem-weil-pbc-truncated-coskeleton-finite-limits: the new node identifies a particular relative nerve as 1-coskeletal; the existing node constructs ordinary coskeleta by finite limits without identifying that nerve.

## Review by Q63

I read Stacks hypercovering.tex, labels lemma-compare-cosk0 (01GC), lemma-acyclicity (01GD), and lemma-acyclic-hypercover-sheaves (01GE), including the paragraph defining K^0 separately and the n=1 comparison. I read simplicial.tex, label lemma-cosk-minus-one (018I), including its full proof by vertex tuples, for the new node. I also read lemma-cosk-up (018B), clauses (3)-(4) and its proof, to check the higher-coskeletality argument. No SGA reference is used. The new lemma is an independent universal-property statement, not a clause of the hypercover exactness conclusion.

For Step 1 I opened the site definition, sheafification definition and sheaf-epimorphism criterion. The first gives pullback coverings and the sheaf equalizer condition; the second gives the factorization/cancellation universal property; the third states exactly that an epimorphism of sheaves of sets is locally surjective. Applying cancellation to the sheafified matching map avoids any unjustified assumption that representables are sheaves. The factorization of each covering member through V_p is part of this item's hypotheses, and no choice of globally compatible lifts is used.

For Step 2 I read the existing Cech free-homology node's whole statement. Its nerve is explicitly the relative fibre product over G, and its degree-zero isomorphism is explicitly induced by the augmentation. Step 1 checks its local-surjectivity hypothesis. The coefficient ring Z is allowed. For Step 3 the finite-limit coskeleton node supplies both the limit formula and the isomorphism of its truncation with the original truncation. The higher-coskeletality calculation is written out by restricting a cone and recovering every entry from its smaller faces; it uses only that formula and its uniqueness, not a new unstated comparison theorem.

For Step 4 I checked that the new node states both parts actually needed: ordinary 1-coskeletality of the relative nerve and the canonical vertex-tuple map for a simplicial augmentation. Its statement allows the presheaf K^1 and the identity map in degree zero. The edge condition gives its augmentation in every degree. The map has the specified degree-one target h_(V_0 x_W V_0), and the p=1 hypothesis gives local surjectivity. The homology-comparison node applies at n=1 because both source and target are now 1-coskeletal; it is no longer being used with the false ordinary-zero-coskeleton identification.

For Step 5 I read the matching/coskeleton node's statement, including theta composed with the canonical map equals the matching morphism. It supplies only the ordinary matching comparison. The extra relative/ordinary identification is proved in the step: for n>=2 every pair of vertices is joined by a proper edge, so the augmentation of a compatible boundary supplies a unique common W-map. This argument fails for n=1, which is why Step 4 is separate. The proof is natural on test objects and matches the canonical map; finite limits of representables are checked by the universal property on Hom(U,-).

Step 6 uses the comparison node with the hypotheses individually checked in Steps 1, 3 and 5. Its statement gives all homology isomorphisms for any commutative ring, so no additional exactness theorem is smuggled into that step. The maps preserve the common augmentation because they preserve the vertices. Step 7 takes the counit statement of the finite-limit node and compares exactly the three chain terms needed to compute homology; at i=0 it uses just terms zero and one. The augmentation compatibility established earlier ensures that the resulting H_0 identification is the one in the claimed augmented sequence.

I tested the new statement with F empty, f the identity, f into a terminal presheaf, and a map whose image omits sections of G. Its coskeletality and vertex-tuple assertions need neither surjectivity nor a subcanonical site. For the item I checked the identity hypercover, a relative Cech nerve and the two-point counterexample above; these distinguish the relative and ordinary zero stages and verify the degree-zero normalization. Every proof step is below 900 characters; no non-elementary long argument has been left inline. All eleven citations are literal portions of the actual statements opened, and all generic off-unit statement uses are declared in split_report.tool_uses. The item statement, its hypotheses and historical blueprint ancestry have been retained.
