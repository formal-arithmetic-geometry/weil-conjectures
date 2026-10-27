# Stage-1 report: lem-sfb-integral-quotient-pullback-face-model

Group NV, 2026-10-22. Direct delivery; author self-review, with independent mathematical review left to the maintainer.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-pullback-face-model.json`: statement, split in eight proof steps. No Mathlib match for the simultaneous six-face unbounded derived normalization.
- `citations.json`: sixteen verbatim statement excerpts, one for each cited node at each proof step.
- `report.md`: this report.

Zero new nodes; zero new Mathlib leaves. Sandbox-local `write_split.py` is the generating script and `searches.jsonl` is the search tool's evidence, not additional repository changes. No unit record is changed: this item is an extracted technical lemma, not the unit's key statement.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, integral quotient pullback terminology, and K-flat terminology found no declaration stating every clause. The generic K-flat and derived scalar results and the Sheaf normalization module do not constitute an attachment for this six-face integral coefficient statement. Project sorry declarations were not treated as finished proofs.

## WANTED

None. The blueprint and the Stacks sources used here are available locally. No SGA source is used.

## Corrections and route

The mathematical statement, hypotheses, and six arrows are unchanged. Its citation for the canonical scalar/pullback comparison previously named only `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. That statement gives monoidality of one ringed pullback, rather than the cross-coefficient comparison. I added `lem-sfb-kflat-scalar-comparison-normalization` to this citation and to `stmt_deps`; its statement supplies exactly the ordinary coequalizer comparison and derived mate normalization needed. This is a C4 citation repair, not a statement dispute.

The eight proof steps realize paragraph (3) of `det-thm-sfb-proper-base-change-integral.proof.md`, through the parent's extraction `lem-sfb-integral-quotient-exchange-comparison`: they supply the actual coefficient projection square and every pullback face of the common-resolution cube. They do not attempt the direct-image faces or exchange theorem, and do not replace a unit-level argument. Generic off-unit tools are declared individually in `split_report.tool_uses`.

No mathematical clause was found false. In particular, scalar extension preserves flatness over the target ring and flat-term K-flatness even for a nonflat quotient map; it need not preserve flatness after restricting scalars back to the integral ring. Step 3 explicitly distinguishes these assertions. No infinite-limit preservation by inverse image is used.

## Searches and reuse

There was no previous sandbox node or report. The current repository item and all its inherited search records were retained, with fresh NV searches appended from the actual `msearch.py` log. Searches used LeanFinder twice, Loogle, LeanSearch, and grep twice. All six completed successfully. Queries and results are copied from `searches.jsonl`; none is invented. The first semantic phrasing concerned common K-flat models for ring-sheaf squares; the second concerned nonflat extension and exact inverse image. The returned module-flatness and ordinary sheaf-pullback declarations do not prove the full item. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:165-181`: `SheafOfModules.pullbackComp` is an ordinary adjoint composition isomorphism, without the K-flat or six-face derived assertions.

Whole-DAG searches for K-flat pullback, scalar comparison, and Tag 0D6D exposed the generic existing nodes now reused. Whole-blueprint searches with `tools/blueprint_refs.py` included `K-flat`, `scalar`, `pullback composition`, `scalar pullback`, `coefficient scalar`, and `quotient pullback face`. No blueprint node states this complete extracted integral six-face model in another form. The nearest ancestor remains `det-thm-sfb-proper-base-change-integral`, with the original parent in `blueprint.from.via`. No new node was necessary: preservation, normalization and finite-word descent already exist. Consequently there are no new-node duplicate pairs to distinguish.

## Review by NV

I read the chapter and proper-base-change unit records, the human's three-level route rule, GOAL.md, the worker/stage-1 contracts, and delivery-errors B-E in full. I read the item's blueprint paragraph (3), the integral-limit proof (especially its warning against claiming preservation of infinite limits), the cartesian-coefficients proof, and the scalar-six pullback proof. I checked the actual Stacks tag-to-label mapping and read sites-cohomology.tex Lemmas 06YS (`lemma-K-flat-resolution`), 0G7E (`lemma-pullback-K-flat`), 06YY (`lemma-derived-base-change`), 0D6D (`lemma-derived-pullback-composition`), 07A4 (`lemma-pullback-tensor-product`) and sites-modules.tex 03EL (`lemma-tensor-product-pullback`). The full simultaneous normalization is an agent assembly from the cited existing nodes, so `proof_origin.by` is `agent`.

For step 1 I opened the statements of `def-sfb-integral-quotient-coefficients`, `sk-def-sfb-pullback-from-point-comp`, `sk-def-sfb-coefficient-morphisms`, `det-prop-sfb-qlbar-colimit-x-integral-limit`, and `lem-sfb-finite-reduction-pullback`. The first really defines the actual quotient by postcomposition and pullback, the next two identify c as components of a natural functor comparison, and the limit node supplies the coefficient-ring identification. The last node is conditional on its adjunction mate sending a continuous function to its relative finite-label quotient map. I checked this condition for the actual projection, and wrote the function-level verification in the step. The source exponent n corresponds to the quotient definition's zero-based index n-1. All uses are untwisted, so no invertibility of ell on schemes is required.

For step 2 I read `lem-sfb-eta-id`, `lem-sfb-eta-comp` and `lem-weil-pbc-mate-pasting`. The first two state the identity and composition equations for the adjuncts, not directly for c. The step explicitly transposes these equations using the cited pasting theorem and injectivity of the adjunction bijection. The coefficient maps and geometric compositors are the very ones fixed by those statements; no arbitrary ring identifications are substituted.

For step 3 I checked `lem-pc-kflat-resolution` supplies flat terms as well as K-flatness, and `lem-weil-pbc-ringed-pullback-preserves-kflat` allows an arbitrary structural ring map. The identity topos and the quotient ring map therefore satisfy its hypotheses. The finite-word induction is written out and applies to any supplied flat-term K-flat P, rather than just the initially chosen resolution. This proves the resolving-class claims without asserting that the quotient is flat over the source.

For step 4 I read `lem-weil-pbc-ringed-topoi-derived-pullback` and `lem-pur-derived-change-of-rings`. Their statements supply invertible computation maps in precisely the direction LF(QP) to Q(FP), and naturality in maps of resolutions. All intermediate inputs satisfy their K-flat hypotheses by step 3. The comparison at a word is the ordered composite of these edge counits, so it uses the same P throughout.

For step 5 I read the full statement of `lem-sfb-kflat-scalar-comparison-normalization`, including its no-flatness clause and the fact that it is the inverse of Q(chi) that equals the scalar-adjunction mate. This fixes the direction of chi used here. Its hypothesis A_X=h^{-1}A_Y is met after transporting along the canonical c from step 1, and similarly for B. `def-weil-pbc-ringed-tensor-section-calculus` supplies actual tensor generators, restriction compatibility, and extensionality. I checked balancing uses the quotient square in step 1 and wrote the two sides out. The argument does not assume that every section is globally pure. I corrected the inadequate tensor-monodality-only citation here.

For step 6 I read the complete statement of `lem-weil-pbc-proetale-derived-pullback-composition`. It expressly states the ordinary representative formula and requires compatible coefficient identifications; these hold by step 2. I checked the composite direction: theta is the inverse comparison for (f',g) followed by the forward comparison for (h,f). The S-coefficient input t_Y(P) is K-flat over S_Y by step 3. Thus the two geometric faces are the ones the item names.

For step 7 I opened the statement of `lem-trf-ringed-kflat-word-comparison-descent`, rather than borrowing from its proof. It explicitly permits identity-topos scalar edges without flatness, supplies the representative equation for ordinary transformations, and preserves both whiskerings and vertical composition. I checked its small-site, ring-map and normalized-counit hypotheses against steps 1, 3 and 4. The six ordinary transformations are listed in the same order as the item's six derived transformations. The node is used as a generic resolving-model tool; nothing about trace transport or a ringed sequence site is required in this specialization. All cited nodes have no dependency path back to the item.

Step 8 is an elementary consequence of the previously proved naturality: it only composes the natural vertex isomorphisms and applies Q to commuting chain-map squares. There is no new acyclicity, resolution-choice, or comparison theorem hidden there. I checked every step length; the longest is 1220 characters, so none triggers the 2000-character long-step review threshold.

Small cases checked were the zero complex, an identity edge, an identity cartesian square, empty schemes, n=1, and the nonflat coefficient quotient A to A/pi. For identities the coefficient and geometric unitors give the expected maps. Zero and empty-site cases use the same additive constructions and require neither nonemptiness nor a nonzero tensor generator. At n=1 the zero-based index is 0 and all maps remain defined. Unboundedness causes no tensor-totalization rearrangement here because the quotient complex is concentrated in degree zero and every edge is applied termwise. No properness, boundedness, completeness, finite Tor-amplitude, or source-ring flatness was inserted.

The B checks required no new-node assertions or searches beyond the item. For C1/C4 every non-elementary input appears in uses and has an exact statement excerpt in citations.json. For D the steps actually construct the finite coefficient square and specialize the common-model calculus, with no new lemma restating an item clause. For E I checked all stated hypotheses and coefficient categories as detailed above. The only edit to statement text is the added accurate citation. No Lean file was written and no compiler, Lake or build command was run.

## Unfinished work

None for this stage-1 split. The referenced generic unsplit nodes remain existing downstream items; they are not asserted to have finished Lean proofs. Delivery awaits the required server dry run and push, whose output is the authoritative delivery result.

## Validation repair

The first completed dry run rejected three citation excerpts shorter than its forty-character minimum. I replaced those excerpts with the full relevant statement or pasting clause. The cited mathematical statements and proof steps did not change.
