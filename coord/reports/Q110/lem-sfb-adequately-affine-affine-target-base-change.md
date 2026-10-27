# Stage-1 report: lem-sfb-adequately-affine-affine-target-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-adequately-affine-affine-target-base-change.json`: item, split; unchanged statement, no Mathlib match.
- `citations.json`: one exact statement excerpt for every proof-step/node pair.
- `searches.jsonl`: actual msearch records; existing imported searches retained in the item, with five new searches appended.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Existing nodes already provide the two substantive algebraic inputs. No Lean files written and no compiler, Lake or library build run.

## Attachments

None. Searched `lean/WeilConjectures/` by the item's blueprint tag and by `adequatelyAffine`, `AdequatelyAffine`, `adequately.affine`, and `adequat`; no adequate-affineness declaration exists there. Sorry declarations would not be attachments.

## Wanted sources

WANTED: Jarod Alper, *Adequate moduli spaces and geometrically reductive group schemes*, arXiv:1005.2398v3, Definitions 3.4.1 and 4.1.1, Remark 4.1.3, Lemma 4.1.8(3), Proposition 4.2.1(5),(6), for lem-sfb-adequately-affine-affine-target-base-change. The named PDF is absent from local literature. I read the primary PDF online at https://arxiv.org/pdf/1005.2398 (v3), printed pp.14--22. The proof is marked agent-written as required for a locally missing source; no document was downloaded or written to the repository.

## Audit findings and changes

The statement is true as imported, including arbitrary nonrepresentable and nonflat h and absence of absolute-diagonal restrictions. No statement correction or dispute is needed. The original node had no proof. The source's general quasi-affine-diagonal base-change argument specializes here to a direct affine-test proof. It is unnecessary to create a node restating Proposition 4.2.1(6), or to invoke adequate-moduli base change, which would have additional structure-sheaf and target restrictions.

The imported blueprint.from.node is null. `tools/blueprint_refs.py ancestor` reports None. I retained its inherited place and via, since those are the item's existing provenance, and recorded this in split_report. I read the latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), and the chapter/unit records. The item is a subordinate algebraic-moduli tool in the inherited alteration chain; this proof does not replace a unit-level step. No realized fields are due, since the item is not the unit key node.

DAG searches by adequate affineness, universal adequacy, affine pushforward, stack fibre products, qcqs, and the relevant source labels found the existing nodes used below. Whole-blueprint searches for `adequately affine`, `adequate`, `power lifting`, `affine pushforward`, `faithfully flat adequately`, `quasi-compact quasi-separated base change`, and fibre-product phrases found no blueprint duplicate of this item. The supporting affine-pushforward and affine-target criterion nodes belong to the same unit. The existing adequate-moduli etale-locality node is unsuitable: it requires a structure-sheaf isomorphism and an algebraic-space target, whereas this item needs only power lifting and has an arbitrary stack target. The composition node also does not state the required arbitrary base change. No new node was created.

The real Mathlib searches returned scheme-level affine-base-change infrastructure and unrelated section/localization lemmas. I inspected `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean`, especially `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange` at line 172; its domain is Scheme and its property is IsAffineHom, so it is not this item. A second semantic phrasing returned localization/power-clearing results on schemes; none states adequate affineness of algebraic stacks. The logged grep hits use the English word adequate in unrelated contexts. Each appended mathlib_searches query is identical to the executed msearch query. No service was reported unavailable.

## Unfinished work

None in the split. The cited unsplit nodes remain separate future items; they are not represented as finished Lean proofs.

## Not duplicates

No new nodes. The split reuses `lem-sfb-stack-affine-algebra-direct-image`, `lem-sfb-affine-target-adequacy-criterion`, and `lem-sfb-algebraic-stack-fibre-products` rather than duplicating them.

## Review by Q110

I checked the item against Alper Proposition 4.2.1(6): the original target T is affine and thus has affine diagonal, but the base-changing stack V need not have any diagonal property. Proposition 4.2.1(5)'s affine argument supplies the actual proof route on affine tests. I also read Alper Remark 4.1.3 and Lemma 4.1.8(3): the global positive-power criterion needs only qcqs and an affine target, not the adequate-moduli structure-sheaf isomorphism. There are no new nodes needing source review.

For step 1 I opened the full statement of `lem-sfb-algebraic-stack-fibre-products`: it expressly gives algebraicity and the triple 2-fibre-product construction for arbitrary stack morphisms. I read Stacks algebraic.tex Tags 04T2/04TF. Reassociating triples simply removes the redundant object identified with the image of the W-object; it identifies the actual projections, so the restricted algebras and section maps match. This is not an identification of an ordinary fibre product with a homotopy fibre product.

For step 2 I opened both cited definition nodes. Adequate affineness supplies qcqs. The quasi-compact-morphism definition quantifies over every quasi-compact algebraic stack, so its application to Z->V->T is legitimate without assuming that Z->T is smooth or representable. The relative diagonal of p is the base change of the relative diagonal of f; every scheme test is a test already quantified in the latter definition. I checked this against stacks-morphisms.tex Tags 050V and 050F, whose proof explicitly uses the base-change diagonal. The elementary step writes out that argument rather than citing the separation-only permanence node for qcqs (that node would not say it).

For step 3 I opened `def-sfb-stack-quasi-coherent-algebra` in full. Its algebras use the big fppf fibred site, local module presentations, and sheaf-local surjectivity. Restriction here leaves the test scheme and its structure ring unchanged; a lifting fppf cover still carries the pulled-back additional map to W_i. This proves preservation of the exact local presentations and surjections in a few lines from the definition. No generic exactness-of-pullback theorem is being silently used. I checked the corresponding conventions at stacks-sheaves.tex Tags 06TP, 06TV, and 06WG.

For step 4 I opened both cited statements in full. The affine-algebra direct-image node explicitly states: arbitrary R->S_i gives an affine stack projection; arbitrary quotient quasi-coherent algebras push forward to quotient quasi-coherent algebras; global section isomorphisms commute with algebra maps and powers. These are exactly the three facts used. I read the source statements and surrounding arguments at stacks-cohomology.tex Tags 0GQY, 077A, 0GQQ, and 0GQR. The affine-target criterion explicitly gives the positive-power lift for every quotient algebra on U. Its hypotheses hold because f is adequately affine, hence qcqs, and T is affine. Thus a power lift transfers as a ring identity, alpha_i(s_i)=(t|W_i)^N_i. Neither the section t nor the quotient algebra is assumed pulled back from U; pushing it forward is the essential argument.

For step 5 I reread the definition's exact smooth-test formula and its etale-cover power-lifting condition. Step 4 gives the lifts on an affine open cover of each arbitrary smooth W. Open inclusions are etale by the displayed local localization/diagonal argument and `def-weil-etale-morphism`, whose full statement I opened. The power exponents may vary with i, as the definition permits. The test W and quotient alpha were arbitrary; combining this with qcqs proves all the stated conclusion. There is no need for a finite atlas of V or a global choice of exponent. Each step's uses list has a verbatim quote in citations.json; I checked each quote as an actual substring of the live cited statement.

I checked delivery-errors B through E individually. B: no new statement-only nodes are needed; all notions used are introduced or have existing definitions, and no claim is dressed up as a definition. C: every non-elementary fact is in the cited statement, no source-proof internals are extracted, and neither adequate-moduli locality nor the separation-only permanence node is misused. D: the proof carries the algebraic argument itself, not a renamed copy of the item; no dependency is created with the same conclusion. E: the proof never assumes h flat, V quasi-compact, U representable, or absolute diagonals affine; it never identifies global power lifting with a structure-sheaf isomorphism. I tested h=id, V empty, U empty, nonflat affine base change R->R/I (including nilpotent quotients), and a nonrepresentable stack V->Spec k. All use exactly the same affine-test argument. Empty tests pose no section-lifting obstruction. All five step texts are below 2000 characters, so no long step hides a separate lemma. I verified the proof has no new-node cycle and no route departure or SGA source.
