# Stage-1 delivery: lem-sfb-cubical-boundary-coordinate-projections

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cubical-boundary-coordinate-projections.json — statement, now split into eight explicit elementary calculations; not a Mathlib match.
- citations.json — four step/dependency pairs, with verbatim quotations from the existing definition statements.
- report.md — this report. searches.jsonl is the search command's own log.

No new nodes; zero Mathlib leaves created.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, cubical/Cubical and coordinate-projection language. The matches concern free sheaves, affine coordinates and other projections, not this lattice chain complex. Inherited node has no Lean declaration or lean_audit to attach. No compiler was invoked.

## WANTED

None. This is expressly an agent-written coordinate calculation, not a claim that Stacks proves the whole lemma.

## Corrections and source audit

The imported proof was empty. Its statement had double-escaped TeX; I removed one escaping layer without changing its hypotheses or conclusions. No mathematical statement change or dispute was needed.

Read literature/stacks-project/more-algebra.tex, the alternating differential immediately preceding definition-koszul-complex, Tag 0623 (verified against tags/tags). Its signs agree with the zero-based q_i convention. The tag is comparison material only; the coordinate maps and regular-action decomposition are verified here, not attributed to that tag. proof_origin.by is agent.

Read the chapter record, unit record, and the current main-20261015 sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3). This is a computation below its open-direct-image integral lattice input. Read the parent lem-sfb-integral-lattice-cubical-contraction, whose steps 1 and 3 use exactly these chain maps and P_r=e. Neither it nor the sibling signed-coordinate-homotopy is invoked, avoiding their reverse dependence on this item. The ancestor command returns None along the existing created.item chain; preserved the imported null from.node and its complete via list and specified the current blueprint location in split_report. No chapter/unit route changed.

Mathlib queries were run through the required msearch.py command: LeanSearch, Loogle, LeanFinder twice with different phrasings, and whole-source grep followed by a focused alternating-face grep. Read every returned signature and inspected AlternatingFaceMapComplex.lean (its simplicial object input and d_squared), HomologicalComplex.lean (complex construction requiring square-zero input), and RepresentationTheory/Homological/Resolution.lean (tuple-based simplicial/bar generators). These do not supply the displayed cubical identities by a one-line specialization. The second semantic query returned geometric ZLattice/fundamental-domain statements, which have extra normed-space data and no cubical maps. The whole-source grep's complete-lattice hit is order theory. Searches appended to the item are taken literally from this sandbox's search log; inherited earlier searches remain intact.

## Not duplicates

No new nodes, hence no new/existing tag-sharing pairs. Searched the whole DAG for cubical, the boundary/lattice language and 0623, and the whole blueprint through blueprint_refs.py searches for cubical, cubical boundary, coordinate and lattice. The contraction parent is stronger and uses this item; the signed-path sibling asserts a homotopy rather than these coordinate identities. No second blueprint statement matches this item. same_as is [].

## Review by N9

I checked B through E of delivery-errors.md, including the duplicated later sections. There is no statement-only child to disguise a clause of the item and no new elementary, duplicate or unsearched node. Every assertion is proved in the item's steps. All steps are marked elementary because each is finite coefficient arithmetic, a basis check, or an instance of one of the two cited definitions, with the actual argument written out. The longest step is under 900 characters; none crosses the 2000-character review threshold.

Step 1 cites def-weil-pbc-free-module: I read its full statement, which gives unique finite coefficient expressions. Explicit extension by a finite sum both constructs the maps and proves their uniqueness/additivity; no universal-property theorem is silently assumed. Every image of a generator is finite, even when the vertex set is infinite.

Step 2 has no citation because it expands the two finite boundaries explicitly: for i<j the two exponents differ by one and the four unsigned vertices coincide. Their pairing covers every ordered pair of distinct deleted coordinates, with no i=i term. Checked a=1, a<=0 and a>r separately; the largest nonzero degree is r and its target exists.

Step 3 cites def-weil-pbc-module-chain-complex-homology only for the condition d_(n-1)d_n=0; I read that condition in its statement and supplied the augmentation calculation 1-1=0 separately. It does not cite a definition to assert exactness or contraction.

Step 4 cites the same definition only for the notion of chain morphism, whose commuting equation is verbatim in its statement. The two membership cases prove the needed equation directly: when i is present only the i-face survives projection and its endpoints reset to the same vertex; when i is absent resetting commutes with every used shift. I checked degree zero and zero groups too.

Step 5 cites nothing: projection commutation follows from the stated two cases, including i=j; the explicit k-coordinate formula follows by applying the reset rules successively. A positive-size subset contains a coordinate and is killed at k=r; a vertex is sent to the origin. Negative-degree identity maps on the zero group are zero. This proves the full-product clause rather than delegating it to a child.

Step 6 cites nothing: associativity/commutativity of addition in Z^r proves both the action law and termwise boundary equivariance. The augmentation remains 1 on each vertex. No equivariance of the coordinate reset maps with all translations is claimed or used (that would be false).

Step 7 cites def-weil-pbc-free-module for its finite-coefficient meaning of the two free groups. It gives explicit mutually inverse coefficient regrouping maps, not just an unsupported 'identification'. The powerset is finite, and every double sum has finite support. Equivariance is evaluated on [v,I]. The basis orbit is free and transitive because the unique translation sending 0 to v is v itself. 'Free integral D-module on one orbit' is thereby specified directly; no group-ring or topological result is invoked.

Step 8 cites nothing: for r=0 there is exactly one vertex and exactly one degree-zero subset. Both epsilon and s are the displayed inverse identifications with Z, and the empty product is the identity, including its zero-group interpretation in all other degrees. Also checked r=1: the edge boundary is [v+1]-[v], its coordinate collapse is zero, and the two projected endpoints coincide. For r=2 and I={1,2}, the four codimension-two vertices occur twice with opposite signs. Negative vertex coordinates do not change any cancellation or reset identity. These cases verify the sign convention, empty products and zero-degree extensions without adding hypotheses.

The four citations.json quotes were tested as literal substrings of the two dependency statements. The proof_deps list is exactly the union of uses; both dependencies are existing Mathlib definition leaves, so there is no off-unit theorem or cycle. No sources from the forbidden SGA route are used. All writes are in this sandbox.

## Unfinished work

None mathematically. The retained version passed the initial current-base dry run at 71b7aab9eec; final validation follows the repair below.


## Repair of return L, 2026-10-23

The return is the single landing/promotion point recorded in coord/returns/N9.md for returned head 3c45ff44478: the reader approved the split, but a side-project completion had not been promoted to the live DAG. I treated that sandbox proof as retained work, not as a completed live item. The required initial dry run exited successfully at 71b7aab9eec. The delivery command builds on the current origin/sheaf-dag and overlays only stage-1 fields, preserving current maintainer metadata; it therefore supplies the requested rebase without a manual repository write or git command.

Compared the retained returned item with the current repository item field by field. The current item is unsplit, with empty proof and proof_deps and null proof_origin/split_report. Its complete statement, source, stmt_deps, created record, chapter/unit and blueprint record agree with the retained version. The delivery supplies the eight retained proof steps, their two dependencies, agent proof origin, six additional previously logged searches, and split metadata. There is no statement correction and no change of route. The original report's escaping correction describes the previous attempt; the current statement already has that normalization.

Re-read both cited current nodes in full, including the definition statements, their Mathlib status, and their source places. def-weil-pbc-free-module explicitly gives unique finite coefficient expressions, including infinite or empty indexing sets; this supports the constructions in steps 1 and 7. def-weil-pbc-module-chain-complex-homology explicitly gives square-zero differentials and the commuting equation for chain morphisms; this supports precisely steps 3 and 4, with no exactness theorem imported. All four existing citations.json quotes are still verbatim substrings. Both nodes remain unmerged Mathlib definition leaves. Thus no changed cited interface forces replacement of a citation.

I checked the actual calculations again: step 2 pairs deletions of i<j with opposite signs; step 4 treats i in I and i outside I separately; step 5 resets only coordinates absent from I and kills a positive-dimensional cell in the full product; step 6 uses commutativity of lattice addition; step 7 explicitly inverts the coefficient regrouping map. Step 8 handles the empty product when r=0. The r=1 edge has boundary [v+1]-[v], and both projected endpoints agree. The r=2 square has cancelling codimension-two faces. Zero and out-of-range chain groups create no extra case or hypothesis. I clarified step 1 to say there are at most r signed differences (at most 2r individual basis terms), to verify integer linearity from coefficients, and to refer to zero groups rather than ambiguously to zero degrees. This is the only change to the retained argument.

Re-read Stacks more-algebra.tex at definition-koszul-complex and its preceding alternating differential (Tag 0623, verified in tags/tags); it remains comparison material, not an unsupported source claim for coordinate projections. Re-read the current blueprint direct-images proof paragraph (3), the chapter and unit records, and the parent's current assembly proof: it still calls this lemma in steps 1, 3 and 5. The coordinate calculation follows the open-direct-image lattice branch and does not cite its parent. The ancestor search still returns null along the inherited chain, so no blueprint ancestry was invented. A fresh whole-blueprint cubical search gives zero matches. There are no new nodes to duplicate or search; prior Mathlib queries and their logged results were read and retained without rerunning unchanged questions.

This repairs the return by delivering the checked split on the current DAG base, with an explicit current-source audit and the finite-sum clarification, for the maintainer to land and promote. It does not mark the live item complete or edit a maintainer-owned record.
