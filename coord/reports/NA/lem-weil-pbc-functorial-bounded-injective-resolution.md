# Stage-1 worker report

## Files written

dag/nodes/sec-proper-base-change/lem-weil-pbc-functorial-bounded-injective-resolution.json — existing statement, now split into eight construction/verification steps; no Mathlib match for the entire assertion.

citations.json — verbatim statements for all proof-step citations.

No new nodes; no new Mathlib leaves. The statement and its statement dependencies are unchanged. No Lean was written, compiled or built.

## Attachments

None. Searches by the exact blueprint tag and by functorial/bounded/injective keywords in WeilConjectures found no declaration giving all clauses under this item's hypotheses. The project kInjectiveResolutionFunctor assumes IsGrothendieckAbelian and its accompanying claims do not preserve every lower bound. Mathlib injectiveResolutions, read at Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean:219–235, is an object-resolution functor into the homotopy category, not the strict complex functor required here. The returned CM5b object-term replacement APIs do not give this entire assertion. Master source was treated only as reference material, never as proof evidence.

## Wanted literature

None. The source texts are present.

## Corrections and findings

The node had no proof. I followed the normalization and iterated cokernel construction of derived.tex, Tag 0141, lemma-functorial-injective-resolutions. I wrote out the verification that its proof omits: the induced maps on kernels and cokernels preserve identities and composition, the resulting object functors preserve zero morphisms, the two bicomplex differentials commute, and the diagonal maps give a functor and natural augmentation.

No statement dispute was found. In particular, additivity of the supplied embedding functor is not needed: after normalization it preserves zero morphisms, which suffices for applying it to complexes. I did not use Cartan–Eilenberg cycle/boundary/homology resolutions or Grothendieck hypotheses; those would impose data absent from the item.

The entire-diagonal coproduct is chosen for each object once. A lower bound proves its existence, but is not an input of the functor. For verification of quasi-isomorphism only, the complex degree is reindexed by that bound. Resolution degree is the first total index, so the total differential is vertical plus (-1)^(resolution degree) times horizontal. This avoids a silent sign change on translation of the complex degree.

## Unfinished work

None in this one-level split. No claim is made that the cited existing nodes' downstream branches have all been formalized.

## Not duplicates

No new nodes. Searches across the entire DAG for 0141, 0133, functorial injective, double complex, total complex and total-column comparison, and blueprint_refs.py searches for functorial injective and injective resolution, found no blueprint statement equivalent to the item. Its same_as remains empty. The existing lem-sc-first-quadrant-column-augmentation was reused instead of creating a bounded-below specialization. The Cartan–Eilenberg total-resolution node has an unnecessary Grothendieck hypothesis, so was not used. The blueprint ancestor was verified with blueprint_refs.py ancestor and its qbar node and original blueprint file were read. The supplied ancestor place describes supporting resolution machinery, rather than a separate step in the finite-coefficient descent proof; the chapter and unit route are unchanged.

## Review by NA

I read derived.tex Tag 0141 (lemma-functorial-injective-resolutions), including its normalization paragraph and its omitted functoriality verification, and homology.tex Tag 0133 (lemma-double-complex-gives-resolution), including its hypotheses and the second-variable variant. The item's hypothesis is exactly a functorial monic embedding into injectives in an abelian category. Its preservation of arbitrary lower bounds is supplied by the normalization J_0(0)=0 and the nonnegative resolution index. No exactness or additivity of J was added. I also read sec-proper-base-change.json and sk-thm-properbasechange.json; this is homological infrastructure below their route, not a replacement for its geometric steps.

For Step 1 I opened def-sp-abelian: its zero object and kernels give the normalized kernel functor, with retraction 1-sr and monicity by cancellation. Step 2 uses the literal lifting definition in def-sp-injective-resolutions: inclusion into J(A), extension, then projection produces the lift into J_0(A). Sending a zero morphism through the zero object proves preservation of zero without assuming additivity.

For Step 3 the kernels/cokernels of def-sp-abelian give the recursive object functors. The displayed quotient equation is checked for identity and composition by cancellation of its epic quotient. Zero objects remain zero inductively. Step 4 uses the same abelian definition to identify the kernel of each differential as the image of the previous embedding; the previous quotient is epic, so this is also the image of the previous differential. These statements were read, not inferred from dependency names.

For Step 5 def-weil-abstract-derived-category supplies the actual complex, chain-map and cohomology definitions. Every square is checked using either the functor equation or the naturality of v_q. The lower-bound induction uses zero preservation from Step 3. No comparison map is chosen by injective lifting here, which would provide only functoriality up to homotopy.

Step 6 cites def-sp-abelian for finite biproducts and def-sp-double-complex-total for the commuting-differential sign convention. I checked the first-index sign and cancellation explicitly. The definition node describes the first-quadrant case; the step itself constructs the integer-indexed extension by the finite-diagonal universal property, so it takes no unstated bounded-below theorem from that definition. On each diagonal, zero summands outside the finite interval give unique omitted legs. Morphisms are defined on the entire fixed diagonal, and identities and composites follow by its universal property even when source and target have different bounds. The augmentation's resolution differential is zero and its complex differential has sign +1.

For Step 7 I opened the entire statement of lem-sc-first-quadrant-column-augmentation. It assumes an abelian category, a first-quadrant bicomplex, a nonnegative complex, an augmentation killed by the resolution differential, its specified map into the total, and quasi-isomorphisms on the augmented resolution columns. After replacing p with a+r, Step 5 provides exactly the first three requirements and Step 4 gives the last; Step 6 supplies the specified total map and chain-map equation. It concludes the quasi-isomorphism of that map, not just existence of some comparison. Its statement imposes no Grothendieck or injective-object assumption. Reindexing back leaves the resolution sign unchanged, identifies all kernels and images degreewise, and handles negative degrees by zero objects. This existing off-unit lemma is declared as a generic tool use in split_report, since this unit has no homological totalization theorem.

Step 8 uses the injective lifting definition again, extending each of finitely many component maps. It proves injectivity of finite sums rather than leaving that as an uncited assertion. An empty diagonal gives zero, which satisfies the lifting property. The interval of possible nonzero indices is empty below every lower bound, proving exactly the final clause. The naturality equations apply to every arrow of any diagram, without a diagram-wide lower bound.

Small cases checked: K=0 yields zero at every stage and in every total degree; a single-term complex in an arbitrary negative degree yields its usual nonnegative resolution starting at precisely that degree; n<a gives an empty diagonal, and n=a gives just E_0(K^a). A supplied J with J(0) nonzero is harmless because the normalization removes that summand; merely using J directly would have broken preservation of lower bounds. Two diagram objects with different lower bounds still have a total map, since diagonal maps use fixed coproducts and do not select a common bound as data. These checks required no statement correction.

Against delivery-errors B–E: there are no new statements requiring separate hypotheses/searches or new-node duplicate justification, all cited nodes were opened and their exact relevant statements are copied into citations.json, the only non-elementary total quasi-isomorphism comparison is a cited existing theorem, and all normalization, cokernel, injectivity, sign and naturality calculations are in the item's own steps. Thus the proof was not moved into a restatement child. New searches were run only with msearch.py and copied from its real log; LeanSearch's HTTP 500 is recorded as unavailable. The item is left split, not reviewed, for the independent reader.

## Second reading by NA

Item statement — checked against derived.tex Tag 0141, lemma-functorial-injective-resolutions, assertion (1), its normalization and finite-diagonal construction; PASS. The abelian-category and functorial monic-embedding hypotheses suffice; the preservation of every lower bound follows from the construction, without additivity or a Grothendieck assumption. No statement dispute.

Step 1 — checked against the normalization paragraph of Tag 0141 and the zero-object/kernel clauses of def-sp-abelian; PASS after explicitly proving the retraction identity by cancellation of k_A.
Step 2 — checked against the entire lifting-property statement of def-sp-injective-resolutions and def-sp-abelian; PASS: composing extension with the retraction gives the required lift, and factoring zero arrows through J_0(0) proves zero preservation.
Step 3 — checked against Tag 0141's iterated cokernels and def-sp-abelian; PASS: the cokernel quotient equation supplies existence, identity, composition and naturality; all recursive functors preserve zero.
Step 4 — checked against Tag 0141's exact augmented columns and def-sp-abelian; PASS: the monic embedding leaves the kernel unchanged, its cokernel has that embedding as kernel, and the preceding epic quotient gives exactly the claimed image.
Step 5 — checked against the complex/morphism definitions in def-weil-abstract-derived-category and the recursion of Steps 3–4; PASS: zero preservation suffices for square-zero differentials and naturality gives their commutation and augmentation compatibility.
Step 6 — checked against finite biproducts in def-sp-abelian and the literal commuting-differential convention in def-sp-double-complex-total; PASS after replacing “the same calculation” with both component equations for I(f). The integer-indexed total is constructed explicitly rather than inferred from the first-quadrant definition.
Step 7 — opened the entire statement of lem-sc-first-quadrant-column-augmentation and homology.tex Tag 0133, lemma-double-complex-gives-resolution, second-variable variant; PASS: reindexing only the complex degree gives precisely the nonnegative complex, resolution-column quasi-isomorphisms, annihilated augmentation and specified total map required. Clarified that independently chosen diagonal coproducts are canonically isomorphic, not literally equal, and that these chain isomorphisms identify the cohomology maps.
Step 8 — checked against the lifting-property definition in def-sp-injective-resolutions and the finite-support construction of Step 6; PASS: extend each finite component and assemble; empty sums are zero, bounds are properties rather than functor inputs, and naturality applies to each diagram arrow independently.
New nodes — none; B1–B7 and new-node pruning have no instances. Existing first-quadrant augmentation is the generic off-unit tool needed here; its use remains described in split_report for the maintainer to register. No top-level tool_uses was added.

Small cases independently checked: zero complexes, nonzero single-term vector-space complexes in degree zero or a negative degree, the boundary total degree n=a, and empty diagonals n<a. A non-normalized embedding J(A)=A plus a fixed nonzero injective in vector spaces illustrates why removing J(0) is necessary. A diagram with two different lower bounds still has total maps defined on the entire fixed diagonals. All checks pass; no field, scheme, or common-diagram-bound hypothesis is being silently used.

Read the chapter and unit _section.md files, the qbar ancestor, all five cited node statements and their source records. Repeated the DAG tag search for 0141 and 0133; there are no proposed new nodes and no restatement child. Independently ran msearch.py LeanFinder with “An abelian category with a functor to injective objects admits a natural quasi-isomorphic replacement of bounded below cochain complexes with the same vanishing degrees”, Loogle with “injectiveResolutions”, and grep with “injectiveResolutions|Injective.*[Ff]unctor|[Ff]unctor.*Injective”. The actual outputs are in searches.jsonl and the item record. Read Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean:219–235: injectiveResolutions has objects of the abelian category as domain and the homotopy category as codomain. Read slopmaster2's kInjectiveResolutionFunctor: its Grothendieck hypothesis and lack of the asserted lower-bound guarantee prevent attachment. Master remains reference material only.

Changes: expanded the kernel-retraction calculation in Step 1; replaced the abbreviated map/differential argument in Step 6 by its two component equations (E5); made the coproduct/cohomology identifications in Step 7 explicit; appended genuine independent search records; refreshed citations.json from the opened statements. The statement, dependency list, construction route, and original worker/review sections are preserved. No new nodes, Mathlib leaves, Lean writes, or builds.
