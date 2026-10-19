# Q18: lem-trf-geometrically-reduced-fibres-limit-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-geometrically-reduced-fibres-limit-descent.json: existing statement, split into four steps; statement and statement dependencies unchanged.
- dag/nodes/sec-trace-formula/lem-trf-geometric-reduced-fibre-locus-constructible.json: new statement-only lemma, unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-geometric-reduced-fibre-locus-base-change.json: new statement-only lemma, unsplit; no exact or one-line Mathlib match.
- citations.json: four entries, one per step citation, each copied verbatim from the cited statement.
- report.md: this report. searches.jsonl contains the actual msearch.py log. prepare.py is sandbox-only preparation, not a delivered project file.

Two new nodes, zero Mathlib leaves. No unit file is changed: this item is a generic approximation input created under another node, not the unit's key statement.

## Attachments

None. Searched WeilConjectures/ in the read-only Slopmaster2 source for the exact blueprint tag, geometricallyReduced/GeometricallyReduced, constructibility of reduced fibres and inverse-limit reducedness. No declaration states the item. The project has smooth-implies-geometrically-reduced and slicing theorems, not the present approximation assertion. Master is reference material only; no master sorry is treated as a proof. The item has no lean_audit record identifying a different declaration.

## WANTED

None for this proof. All mathematical inputs used here were read in the available Stacks .tex sources. Temkin's historical reference is preserved as inherited ancestry, not quoted as an unread proof input.

## Findings and changes

The imported item was statement-only. Its statement is correct, including the absence of flatness, and has not been corrected or weakened. The source route is valid. Stacks 0579 gives a locally constructible good locus without flatness, and 0576 gives its exact inverse-image equality under arbitrary base change. To use the existing DAG node for 05F4, whose statement asks for a globally constructible subset, the new 0579 input is stated on a qcqs base. A finite affine cover is a finite cover by retrocompact opens on a quasi-separated scheme; 053W promotes affine-local constructibility to constructibility on that base. This strengthening of the source's local form is justified by that topology lemma; no Noetherian assumption is substituted.

The source uses geometrically reduced scheme-theoretic fibres while the item uses reduced geometric fibres over an algebraic closure. I checked the convention rather than silently changing it: 035X (2) iff (6) proves the algebraic-closure criterion in positive characteristic; in characteristic zero the base field is perfect and 020I applies after descent of reducedness from its field extension. The new nodes explicitly use the item's geometric-fibre wording and cite these source places. A reduced geometric fibre is not being replaced by a merely reduced ordinary fibre.

The existing node lem-weil-pbc-limit-contained-in-constructible is an off-unit generic tool; it is declared in split_report.tool_uses. Its statement, not an argument hidden in its proof, is the precise all-later-stages containment needed. There is no scheme-theoretic factorization deduced from an image inclusion.

The nearest blueprint ancestor is lem-trf-local-term-locality. The inherited chain reaches this item through the Temkin/noetherian-reduction branch. I read the current main-20261015 ancestor proof and unit sk-i-curve-zero and preserved that historical ancestry: this delivery does not change the chapter/unit route or claim that the current unit's contracting-correspondence argument is replaced by approximation. blueprint.from.place is already precise; both new children carry this ancestor, the item's full via chain with the item prepended, and an exact description of the noetherian-reduction input they serve. Whole-blueprint searches for geometrically reduced, locally constructible, 0579, 0576, 053W, 0384, 035X and 020I found no blueprint node stating either new input; same_as is [] throughout this delivery.

## Not duplicates

lem-trf-geometric-reduced-fibre-locus-constructible vs lem-trf-geometrically-reduced-fibres-limit-descent: constructibility of one family's good locus is a general input on a qcqs base, not the existence of a late stage of an inverse system; it contains no inverse limit or eventual conclusion.

lem-trf-geometric-reduced-fibre-locus-base-change vs lem-trf-geometrically-reduced-fibres-limit-descent: exact equality of good loci under one arbitrary base change is a general input requiring no inverse system or finite presentation; it does not assert eventual descent.

lem-trf-geometric-reduced-fibre-locus-base-change vs lem-trf-geometric-reducedness-local-base-change: the existing statement is an equivalence for two particular localizations of tensor-product rings at points, formulated using every field extension. It does not state the global fibre-locus equality for arbitrary scheme morphisms or the chosen-algebraic-closure geometric-fibre test. It is related foundational material, not an exact statement or one-line specialization of the new scheme-level input.

lem-trf-geometric-reduced-fibre-locus-base-change vs lem-trf-geometric-field-stalk-descent: the existing node assumes a finite type algebra and a maximal ideal and concludes residue-field finiteness/separability and a local-ring equality when a geometric local ring is the algebraic closure. It does not state preservation and reflection of reduced geometric fibres over arbitrary base points.

lem-trf-geometric-reduced-fibre-locus-base-change vs lem-weil-pbc-separable-tensor-purely-inseparable-field: the existing node says that a particular tensor product of separable and finite purely inseparable field extensions is a field of prescribed degree. It has no scheme fibre locus or arbitrary base-change equality.

lem-trf-geometric-reduced-fibre-locus-constructible vs lem-trf-geometric-reduced-fibre-locus-base-change: the first asserts constructibility under quasi-compact local finite presentation and qcqs base hypotheses; the second asserts an equality under arbitrary base change without those hypotheses. Sharing geometric-fibre conventions is not a shared conclusion.

lem-trf-geometric-reduced-fibre-locus-constructible vs lem-trf-geometrically-reduced-fibre-locus: the concurrently landed Q04 node assumes a finitely presented ring homomorphism and concerns its affine fibres. The new node concerns a quasi-compact locally finitely presented morphism with arbitrary source and a qcqs base that need not be affine; even the source morphism need not be quasi-separated. It is not a specialization of the ring statement. Passing from affine presentations to this assertion requires a geometric affine-cover comparison of all fibres and constructible gluing on the non-affine base, so the existing statement does not directly supply the input taken by Step 1.

lem-trf-geometric-reduced-fibre-locus-base-change vs lem-trf-geometrically-reduced-fibre-locus: the concurrently landed Q04 node gives an equality for fibres of a finitely presented ring map under change of the coefficient ring. The new statement gives equality for arbitrary scheme morphisms and arbitrary base change, with no finite-presentation or quasi-compactness assumption at all. It is not a special case of the affine finitely presented result; in particular the general reflection assertion cannot be obtained from the existing statement merely by substituting its objects.

## Review by Q18

I read Stacks more-morphisms.tex, lemma-geometrically-reduced-constructible (0579), lemma-base-change-fibres-geometrically-reduced (0576), and the proof of lemma-Noetherian-approximation-geometrically-reduced (05FG), which uses exactly this good-locus argument after a model is chosen. I also read limits.tex lemma-limit-contained-in-constructible (05F4), properties.tex lemma-locally-constructible (054C), topology.tex lemma-collate-constructible (053W), and varieties.tex lemma-geometrically-reduced (035X), lemma-perfect-reduced (020I), and lemma-geometrically-reduced-upstairs (0384). The constructibility source's hypothesis is quasi-compact and locally of finite presentation, both present for q_a. It makes no flatness assumption. The base-change source imposes no finiteness or surjectivity condition and proves both directions using the residue-field extension, so it applies even when a projection from the inverse limit is not surjective.

For Step 1 I opened the newly written constructibility statement and checked that it gives constructibility of precisely E_a over the given qcqs base. The source first gives local constructibility; the new statement's global form uses the finite retrocompact affine cover and 053W as explained above. This non-elementary input is a node, not hidden in an elementary step.

For Step 2 I opened the base-change statement and matched f=q_a, g=p_a, X'=Y and f'=q. Its displayed equality gives p_a^{-1}(E_a) as the reduced-geometric-fibre locus. The hypothesis makes that locus all of S, and the image containment is then the elementary set-theoretic implication p_a^{-1}(E_a)=S => p_a(S) subset E_a. I did not assume p_a is surjective or use a node about reduction of total spaces.

For Step 3 I read the whole existing lem-weil-pbc-limit-contained-in-constructible statement: all stages must be qcqs, all transitions affine, the cone must be limiting, E_a constructible, and the limit image contained in E_a. Each is an explicit item hypothesis or the result of Steps 1-2. Its conclusion quantifies over every i' >= i_1, not just a single stage. That exact sentence is copied into citations.json. Using the original full system at index a avoids an extra cofinal-tail comparison lemma.

For Step 4 I again checked the base-change node with g=p_ia. It gives the exact good locus for q_i. The image containment of Step 3 makes this inverse image all of S_i. This proves the same conclusion simultaneously for all i >= b, rather than implicitly using an uncited persistence theorem. All four steps are explicitly non-elementary because they apply cited substantive inputs; none exceeds 2000 characters or hides a further comparison.

I checked the definition statements cited by the two new nodes: def-pc-scheme, def-sbc-locally-finite-presentation, def-weil-pbc-scheme-conventions, def-weil-geometric-fibre, def-pc-base-change, def-pc-reduced-scheme and def-weil-constructible-subset. Every object is introduced in the new statement. Both new nodes have empty proof and proof_deps and no proof sketch inside their statement. The source, not a tag used as a definition, supplies the convention comparison. No hollow definition or Lean file is introduced.

Small cases checked: (a) Y_a empty gives E_a=S_a and b=a works. (b) Empty geometric fibres are reduced, so removing points of the image creates no spurious bad locus. (c) S empty need not make S_a empty; 05F4 is still applicable to the empty image and kills the constructible bad locus at a later stage. (d) A constant inverse system gives the original hypothesis as its conclusion. (e) Over an imperfect field, Spec(k[t]/(t^p-c)) for c not a p-th power is an ordinary reduced fibre with a nonreduced geometric fibre; both new statements correctly use the latter and mark the point bad before and after field extension. (f) Nonflat finitely presented families are allowed by 0579, and the proof only takes their loci, never their openness. (g) A non-surjective g: T' -> T only tests points in its image; the equality of inverse images remains the right statement. None of these cases needs a hypothesis not present in the node.

Mathlib searches were actually run through the required msearch.py command and are retained in searches.jsonl. I read all returned hit lists, tried a second meaning-based phrasing for each new node and the item, and inspected the plausible source files: Geometrically/Reduced.lean and Basic.lean, Morphisms/FinitePresentation.lean (Chevalley, lines 121 and 165), RingTheory/Nilpotent/GeometricallyReduced.lean, and AffineTransitionLimit.lean (eventual equality, line 635). Chevalley's theorem concerns the image of a known constructible set, not constructibility of this good locus. Global base-change stability does not reflect a pointwise good locus. The ring-level algebraic-closure criterion does not state the scheme-locus assertion; the pinned local file even records an outstanding equivalence TODO for the general ring definition. Hence neither new input is being incorrectly classified as a Mathlib leaf. Existing item search records were retained; its recorded queries were re-run and read with the actual log.

The B-E audit found no statement dispute. I corrected the potential C4 local/global mismatch before writing the nodes by using a globally constructible good locus on a qcqs base, and I used the existing all-later-stages conclusion of 05F4 verbatim. The two new nodes are generic facts of a single family/base-change square, not clauses restating the item's approximation conclusion. All citations have literal quotes, proof_deps is the union of uses, there is no dependency back to the item in either new node, and the generic off-unit tool is declared for independent review.

## Unfinished work

The two general inputs are intentionally statement-only unsplit nodes, as required by one-level stage-1 splitting. No part of the item's proof is omitted. The initial server dry run passed (receipt d176a36653). The subsequent push attempt detected the concurrently landed affine Q04 node lem-trf-geometrically-reduced-fibre-locus. I read its entire statement and recorded both comparisons under Not duplicates: its hypotheses and domain are strictly narrower than either new scheme-level input. No node statement or proof step changed in response; the general-scheme input remains necessary for the item as stated. A final dry run and push follow this report update.
