# Q36 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-derived-projection-formula.json: item split, seven proof steps; not in Mathlib.
- citations.json: 26 citations, each with a verbatim excerpt of the cited statement.
- searches.jsonl: retained actual msearch.py records; additional item searches are appended to the inherited searches in the node.
- report.md: this report.

No new nodes and no new Mathlib leaves. No Lean files written; no compiler, Lake, local DAG checker, or repository git command run.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for affine derived projection-formula terminology. Existing scheme projection-formula material concerns schemes with their Zariski structure sheaves; finite-coefficient projection formulas concern constant coefficients. Neither states the item for algebraic spaces with the small-etale structure sheaf and all unbounded quasi-coherent complexes.

## WANTED

None.

## Corrections and route

The imported item was statement-only and its assertion is true. Its statement is retained verbatim. In the sentence defining the projection arrow, the module N is understood on Spec A by its associated etale sheaf a_A(N); the proof spells out that typing and obtains the claimed D(A) arrow by derived global sections. No hypothesis is added or conclusion changed.

Read the current blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its det-thm-sf-ctf-stability-direct-images material. This item is a supporting structure-sheaf calculation, not a constant-coefficient six-functor theorem. Its inherited origin describes the Tag 0D3F input in the direct-image alteration branch. Followed Tag 08IN's own affine generation argument. The right-adjoint statement already in the DAG implies the direct-sum input as a generic colimit argument; this does not replace a step of the blueprint unit. Its source, Tag 0E55, derives the right adjoint from direct-sum preservation and compact generation and does not use the projection formula. There is no mathematical circularity in using this stronger existing input here.

blueprint_refs.py ancestor reports None: the inherited created.item chain has no recognized imported ancestor. I retained the inherited from.node=null, its detailed place and full via chain, and same_as=[]. Searches over the entire imported blueprint for projection formula, affine projection, direct sums, pushforward direct sums, quasi coherence pushforward, flat morphism, flat pullback, and derived module free generation found no blueprint statement of this algebraic-space affine module formula. In particular lem-pc-projection-formula is for schemes and cannot be applied to X here.

## Not duplicates

No new nodes. All prerequisites are reused. In particular I did not create a Tag 08FB direct-sum lemma: lem-sfb-qcqs-space-pushforward-right-adjoint and lem-weil-pbc-left-adjoint-preserves-colimits already give the required preservation in two lines. I also reused lem-pc-derived-module-free-generation instead of recreating Tag 09PB, and lem-sfb-affine-etale-derived-module-realization for the affine equivalence.

## Mathlib searches

Read the inherited search results, including the ordinary scheme-module adjunction and affine-limit hits. Ran additional item queries through the required msearch.py wrapper: LeanFinder on the affine unbounded quasi-coherent projection formula; LeanSearch on derived global sections commuting with derived module tensor; Loogle on SheafOfModules, DerivedCategory; and grep on projectionFormula|projection_formula|AlgebraicSpace under AlgebraicGeometry. LeanFinder returned affine-transition-limit and presentation-map facts, LeanSearch returned ordinary global-sections definitions and flat-module tensor exactness, and grep returned no hits. These do not establish this algebraic-space derived theorem. Loogle returned HTTP 502 and is recorded as unavailable. An exploratory LeanFinder query on flat algebraic-space pullback is logged but not asserted as an item match or a new-node search; I ultimately proved the needed coefficient exactness from existing chart and flat-tensor statements.

## Review by Q36

I read spaces-perfect.tex Tag 08IN (lemma-cohomology-base-change), including its construction of the counit projection morphism, its direct-sum and triangle paragraphs, and its reduction to A[k] by More on Algebra Tag 09PB. I also read its flat-pullback paragraph before lemma-check-quasi-coherence-on-covering, the coproduct statement/proof lemma-quasi-coherence-direct-sums, and Tag 08FB. I read spaces-duality.tex Tag 0E55 (lemma-twisted-inverse-image), including its Brown/direct-sum argument, and more-algebra.tex remark-P-resolution in full through its three-property criterion. The affine comparison is spaces-perfect.tex Tag 071Q with perfect.tex Tag 06Z0 (lemma-affine-compare-bounded). For the coefficient clauses I checked spaces-morphisms.tex Tag 073C and sites-modules.tex Tag 04JC, as well as the existing nodes' stronger affine-chart route. No SGA source is used.

I opened and read the statement of every cited node. Step 1 uses affine-etale module realization for exactness and affine sections, the scheme Zariski/etale comparison for compatibility with scheme pullbacks, the affine pullback-sections formula for its actual tensor map, space-module pullback quasi-coherence, the scheme flatness affine criterion, and flat tensor exactness. These statements apply to every affine etale scheme chart; flatness is provided precisely by the item's chartwise hypothesis. The sheaf gluing argument handles exactness locally and does not assume arbitrary evaluation on sections is exact.

Step 2 uses exact derived factorization for the already proved exact functor H, the ringed-topos K-flat pullback/tensor theorem for preservation of flat-term K-flat resolutions and comparison with iterated scalar extension, and the K-flat-resolution node for existence. The ordinary adjunction to A-module-valued sections is written as the explicit mutually inverse formulas on tensors. This gives the degree-zero derived pullback without any flatness assumption on N. The one-point site is small in the same module universe.

Step 3 uses the entire affine-etale derived equivalence, not merely its degree-zero sections clause, and the ringed-topos tensor comparison. It identifies the affine projection mate by full faithfulness and the actual counit, using the exact projection-mate node. That node says both that the transformation is the specified adjunct and that its tensor-unit component is the identity. Therefore the dictionary identifies maps, not only objects. The citation excerpt for the affine equivalence includes both exactness and the unbounded equivalence/quasi-inverse clauses.

Step 4 uses the qcqs-space right-adjoint statement for both quasi-coherent preservation and the extra right adjoint. Its hypotheses are satisfied by X and Spec A, viewed as spaces over Spec A. It does not require X proper, Noetherian, separated, or of finite presentation. The perfect-localizing-generation statement is used ONLY for its explicit ambient-coproduct clause, not for a new generation argument. Left adjoints preserve colimits, so the already given right adjoint to Rf_* supplies coproduct preservation. Ringed-site closed derived tensor supplies tensor adjoints on the structure-sheaf sites and on the point, and the projection-mate node supplies the derived pullback adjunction. The space-derived-qcoh-pullback-tensor statement ensures the arguments to Rf_* remain in D_QCoh. The affine equivalence supplies coproduct preservation and identifies its values. All coproducts are set-indexed in the fixed universe, including the empty one.

Step 5 uses exact projection-mate data for exactness, the connecting square, unit normalization and shift compatibility; exact factorization and exactness of a_A allow precomposition with the affine equivalence. Step 6 uses exactly the compatible-shift triangle two-out-of-three theorem and the full unbounded module-generation theorem. Coproduct and retract closure are proved explicitly by coprojection naturality and the displayed inverse. Thus no bounded-resolution assumption or unstated telescope lemma is concealed in this step.

Step 7 uses canonical derived pushforward composition, and the statement of ringed-projection-tensor-composition, which explicitly includes naturality and the projection-composition equation. Applied to f followed by p_Y, that equation identifies our map with the canonical projection mate for p_X. Step 3 supplies its first factor. This is why the result has the required naturality for every N to N', rather than just a family of abstract isomorphisms.

I checked the edge cases X empty, E zero, N zero, A the zero ring, arbitrary infinite module N, and E unbounded in both directions. In the first four cases the tensor, pullback and sections expressions have the corresponding zero values and the unit/generation argument still applies. For general N no flatness or finite presentation is assumed on N; flatness is used only for the chart rings over A. Coproduct closure never assumes intersections of affine charts are affine. Every step is below 2000 characters, and no extra derived comparison or boundedness claim is hidden in a long step. I checked delivery-errors B through E against the final node, sources, and citation excerpts: no new statement-only node to audit, no duplicate, no clause of the item moved into another node, no definitions cited as theorem substitutes, and no changed statement.

## Unfinished work

None of the requested stage-1 split remains. Existing prerequisite nodes may remain unsplit in the project; this is the prescribed one-level split.
