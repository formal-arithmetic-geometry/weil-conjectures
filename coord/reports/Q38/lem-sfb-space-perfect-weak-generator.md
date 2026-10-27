# Stage-1 report: lem-sfb-space-perfect-weak-generator

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-weak-generator.json: retained seven-step split of the unchanged statement, using existing nodes throughout. Zero new nodes and zero Mathlib leaves.
- citations.json: retained seventeen verbatim quotations covering all proof-step/dependency pairs.
- report.md: current source review and validation, replacing the historical blocker narrative. The complete previous report remains in retained/ alongside all earlier proposed nodes, diagnostics, scripts, search logs and search outputs.

## Attachments

None. A current whole-project search by the exact blueprint id and perfect-generator terminology finds no declaration for general algebraic spaces. AlgebraicGeometry.exists_perfect_generator in lean/WeilConjectures/AlgebraicGeometry/PerfectGeneratorExists.lean:50 explicitly takes X : Scheme, and therefore supplies only the scheme input rather than an attachment for this item.

## WANTED

None: the necessary Stacks sources and current blueprint are available locally.

## Corrections and provenance

The mathematical statement and statement dependencies agree with the live item, which is unsplit and has no released repair note. I retained the proof, citations, provenance and logged searches from the earlier attempt. The delivered tree contains only the assigned item: the former open-retract and support-image proposals were already archived after equivalent live inputs became available. I introduced no duplicate, elementary, or conclusion-restating node.

The mandatory initial dry run in this resumption completed successfully: OK (not pushed), commit 262e3449e70, server preflight passed. The prior nine-node cycle is no longer a blocker. In the current comparison node, the proof dependencies no longer include lem-sfb-qcqs-space-pushforward-right-adjoint; the repaired interface states precisely the equivalence and direct-image comparison this item uses. No outside node was edited by Q38.

I read the current chapter and unit records and the latest blueprint stability unit and direct-image detail, snapshot 7284bb09daf97437d544c51882b325f9c52cd345. Their current text differs from parts of the inherited ancestry description, which remains historical provenance. This item is a supporting perfect-test prerequisite, not the unit key statement, and does not change a chapter, unit route, target, or realization record.

The saved searches.jsonl and item result files were inspected and reused. The two semantic phrasings return derived-category and t-structure declarations; the grep hits concern perfect fields and unrelated pairings; the Loogle query reports an unknown identifier and supplies no usable result. The LeanSearch responses likewise supply no perfect weak-generator theorem for algebraic spaces. The node preserves the exact earlier queries and their recorded outputs. No fresh Mathlib search or new match is claimed.

## Not duplicates

There are no new nodes in this delivery. The proof reuses lem-sfb-space-perfect-open-retract and lem-sfb-space-supported-etale-excision rather than delivering the archived proposals.

## Review by Q38

I read Stacks spaces-perfect.tex, Tag 09IY (theorem-bondal-van-den-Bergh), including its full proof and omitted-detail sentence. I also read Tag 09IX (lemma-direct-summand-of-a-restriction), Tag 08GG (lemma-pushforward-with-support-in-open), and Tag 08HK (lemma-pushforward-perfect). The retained argument follows distinguished-square induction, open extension, supported Koszul pushforward, and orthogonality. It expands the source's omitted local-unit check into the cover-and-cone argument in step 6. No SGA source is used and no source statement requires correction.

For step 1 I opened lem-sfb-space-qcqs-distinguished-square-induction: its statement explicitly includes the empty affine case and places all four square vertices in the qcqs domain. The property in the proof is invariant under isomorphism, and the identity etale map includes the desired X. For step 2 I checked the scheme generator and def-pc-generators give detection by every shifted Hom; moving the shift changes its sign. The unbounded derived etale-Zariski equivalence is fully faithful with its canonical unit and counit, and etale-detects-perfect supplies the precise change of perfectness. An affine scheme meets the scheme theorem's qcqs hypotheses.

For step 3 I read the open-retract statement: it gives both maps and their composite identity under exactly the qcqs and quasi-compact-open assumptions present. The intersection W inside affine V is quasi-compact by the induction domain, so its principal-open cover has a finite subcover. The Koszul restriction-zero statement applies to that finite list; the site equivalence carries its restriction vanishing to the small etale site. Finite free Koszul terms satisfy the cited local perfectness definition directly. This construction does not assume W affine.

For step 4 I checked supported-etale-excision states the full derived comparison with extension by zero, both restriction conclusions, and the Hom bijection for every integer. Its hypotheses are the elementary square and the already proved vanishing on W. Local bounded representatives on the jointly covering U and V prove perfectness of the supported pushforward; their finite direct sums prove perfectness of G. The perfect-objects-compact statement explicitly includes quasi-coherent cohomology, which is the only clause this step takes from it. The summand inclusions and projections give the two Hom vanishings, and the excision Hom formula with integer -n supplies the needed vanishing on V.

For step 5 I read Koszul orthogonality with its ambient scheme and affine chart both V, and other open W. Its quasi-compact-intersection hypothesis holds. Chart calculus states preservation of quasi-coherent cohomology under pullback. The site equivalence explicitly intertwines restriction and qcqs direct image, so the conclusion is the canonical open-adjunction unit on the etale site. In step 6 chart calculus gives etale base change compatible with units and counits; on U the unit is identity, and on V it is the preceding unit isomorphism. The two members cover Y because the etale map is an isomorphism over the complement. The cone has zero cohomology sheaves on this cover, hence globally by the sheaf axiom, which proves invertibility. Step 7 uses the stated derived adjunction and the explicit composite ri=1 to make every shifted map from P vanish; its inductive detection then forces E|_U and E to be zero.

I verified each of the seventeen citation quotations is a literal substring of its current live statement, and that the quotation pairs equal the proof's step/use pairs exactly. Proof dependencies are the union of the uses. The seven step lengths are 619, 647, 800, 1079, 603, 754 and 567 characters; none hides a long-step lemma. Scheme generation and the two Koszul results are the representable tools needed by the source route, as explained in split_report.tool_uses for maintainer review.

The empty space, empty or full U, empty Koszul list, and a cover containing D(1) satisfy the argument. In particular, the empty list covers an empty W, while D(1) yields an acyclic Koszul complex when the closed complement is empty. No noetherian, boundedness, affine-intersection, or relative-separation assumption is added. Reading delivery-errors B through E against these steps found no uncited non-elementary input, proof-only citation, false hypothesis application, or circular invocation. All writes in this resumption are confined to this sandbox; no Lean code, compiler, build tool, git command in the repository, or agent delegation was used.

## Unfinished work and validation

There is no unfinished part of this one-level split. Existing dependency items retain their own stage-1 obligations. The first resumed full dry run passed and exited before any later invocation. A final report-inclusive no-push validation and the authorized direct delivery follow; only a successful server result will be reported as delivered.
