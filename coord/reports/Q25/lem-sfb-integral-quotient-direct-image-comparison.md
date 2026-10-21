# Stage-1 delivery: lem-sfb-integral-quotient-direct-image-comparison

Group Q25; 2026-10-21. Direct delivery; no second worker, Lean writing or compilation.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-direct-image-comparison.json`: statement, six-step split, no Mathlib match.
- `citations.json`: verbatim statement extracts for every citation in every step.
- `searches.jsonl`: five actual searches made with the required msearch command; the item's inherited searches are retained.
- `report.md`: this report. `write_split.py` is sandbox-only preparation material.

No new nodes and no new Mathlib leaves. The item statement and its statement dependencies are unchanged. Its existing blueprint ancestry and metadata are retained, and `same_as` is empty after searching the whole imported blueprint. It is not a unit key node, so no unit record is changed.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact item tag and for quotient/direct-image, reduction/pushforward and perfect-projection terms. No declaration states this internal-module, unbounded quotient-linear mate with its normalization and tower compatibility. The hit `exists_derivedTensor_precomposition_projection` is a scheme structure-sheaf tensor-precomposition factorization, not this statement. No source declaration with a sorry was counted as an attachment.

## WANTED

None for this split. All proof tools used here already have DAG nodes. The local-field input is taken from the existing DVR and finite-quotient nodes; their broader literature obligations are not new obligations of this item.

## What needed repair

The item was unsplit, with no proof. The blueprint paragraph (1) gives a cone argument in the integral coefficient category; that alone does not identify the actual quotient-linear morphism, because derived restriction of scalars need not be faithful on morphisms. I supplied the specific balancing/adjunction computation before applying conservativity to isomorphisms. I did not assert that forgetting scalars detects equality of morphisms.

For successive quotients, a further danger is claiming a regular-element resolution of the smaller quotient over the larger one. For example, multiplication by the residue of a uniformizer on A/(pi^2) is not injective. The proof instead uses unrestricted K-flat change of rings and its normalized units, then pastes the pullback squares and takes their mates. It does not require S_m to be perfect over S_n or the relative mate to be invertible at arbitrary S_n-inputs.

No statement dispute or source correction is needed. No clause, hypothesis or coefficient category has been changed. No SGA source is used.

## Not duplicates

No new nodes. Existing nodes cover every non-elementary fact needed by this split. In particular the broader perfect-projection node, completed-constant reduction node, internal/section comparison nodes, successive derived quotient normalization and mate-pasting node are reused. The nearby integral quotient projection-comparison node is not cited: it concerns a second arbitrary tensor input and depends on this item.

Whole-DAG searches included the item notion, uniformizer, quotient comparison, completion-flat and composition tags. Whole-blueprint searches included `reduction direct image`, `quotient`, `projection formula`, `quotient.*direct.image` and `completed.*reduction`. The broad searches returned ordinary finite/perfect projection and coefficient nodes; none is the full quotient-linear comparison being split here. No new node restates the item's clauses.

## Mathlib searches

I read the five msearch results. LeanSearch returned ordinary sheaf/presheaf module pushforward and its ordinary composition associativity. I read the ordinary sheaf pushforward definition in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`; it has no derived scalar/direct-image assertion. LeanFinder returned exact-functor derived-category maps, localization comparisons, linearity and Ext maps. Those supply generic constructions rather than this comparison. Loogle for `"projectionFormula"` returned no hits. The CategoryTheory grep returned no hits. The whole-Mathlib grep found only a manifold comment and the Witt-vector Frobenius/Verschiebung projection formula. Those are unrelated. These searches provide a second phrasing beyond the item's retained upstream searches; all newly recorded queries are exactly the logged query text. All five services/commands completed successfully.

## Review by Q25

I read the chapter and proper-base-change unit, the current main-20261015 integral proof (paragraphs (1) and (3)), the current integral-limit blueprint node and the older perfect-projection blueprint proof. The split follows the same uniformizer cone route and adds the quotient-action and canonical-map details that the extracted item requests. I also read Stacks sites-modules.tex Tag 093M (`lemma-completion-flat`) and 093J (`lemma-constant-exact`), and sites-cohomology.tex Tags 06YQ (`lemma-bounded-flat-K-flat`), 0G7E (`lemma-pullback-K-flat`), 0D6D (`lemma-derived-pullback-composition`), 07A6 (`lemma-adjoint`), 0D6E (`lemma-derived-pushforward-composition`), 0FPI (`lemma-adjoints-push-pull-compatibility`), and 0B56/0944 (the actual projection arrow and perfect projection formula). For formal pasting I read Mathlib's `mateEquiv_vcomp` through the already existing mate-pasting node. There are no new-node sources to certify. The proof is honestly marked agent-written: Stacks does not state this whole internal-module normalization as one theorem.

For step 1 I opened the DVR, finite-quotient, integral-limit, completed-constant reduction and flat-scalar cyclic-resolution node statements. They respectively supply the regular scalar, finiteness, the precise inverse-limit presentation, the flatness/canonical augmentation and the K-flat two-term complex. A DVR is Noetherian because all its ideals are principal. The nonzero scalar hypothesis holds for every positive power of the chosen uniformizer. The canonical augmentation is the finite projection specified in the item, not a replacement quotient map.

For step 2 I opened the internal/section tensor comparison, derived change-of-rings, derived pushpull normalization, cartesian coefficient and normalized monoidal-composition statements. The tensor equivalence preserves flatness and K-flatness; the pushpull normalization explicitly identifies the independently derived adjunctions and counits for arbitrary schemes. I deliberately did not use `lem-pd-module-ringed-topos-derived-comparison`, whose statement has finite-type field hypotheses absent here. The selected two unrestricted comparison nodes supply what is needed. Finite quotients have their discrete condensed coefficients, and cartesianity is used only for untwisted coefficients, so no invertibility of ell on the schemes is introduced.

For step 3 I opened the ring-sheaf change-adjunction and tensor-pullback statements, and reused the normalized derived monoidal-composition statement. The former specifies b on identified-coefficient inverse images. The latter statements provide flat-term K-flat computations and canonical composition/tensor coherence, so the displayed balancing identity is an equality of the specified maps in the derived category. It uses no arbitrary choice of an isomorphism between endpoints.

For step 4 the ring-sheaf change-adjunction statement explicitly gives the adjunct of the restricted t composed with b inverse: it is d composed with restriction of the S-adjunct. Substituting the t in the item gives the displayed counit-tensor map, and the projection-formula definition explicitly names its adjunct. The change-of-rings node gives the scalar-extension computation on K-flat models. This verifies C4 for the crucial canonical-map claim, rather than citing a definition of restriction for an uncited comparison theorem.

For step 5 I opened the complete current statement of the perfect-projection node and verified its hypotheses for the entire adic system: A is Noetherian, each quotient is finite and therefore torsion as an additive group, and every quotient has the displayed two-term finite free A-resolution. Its statement allows unbounded inputs and arbitrary morphisms. The change-adjunction node explicitly says restriction reflects isomorphisms and d is invertible. Thus this step proves the quotient-linear mate is invertible; it uses reflection of isomorphisms only.

For step 6 I opened the successive quotient-normalization, derived monoidal-comparison, mate-pasting and derived coefficient-adjunction statements. The first gives precisely the balanced representative formula and composite-unit normalization; the second provides comparison coherence; clause (1) of mate pasting gives exactly the composite of the two right squares. The displayed equation has source E_Y D_n,Y F_R K and target F_Sm D_m,X K in D(S_m,Y), so all factors have the required coefficient category. The coefficient-adjunction node provides the normalized unit when converting to reduction-unit maps. No missing flatness assumption is imposed on the quotient-to-quotient map.

I checked the cases n=m, f the identity, the zero complex and empty schemes. For identity f the balancing map and counit identify rho with the identity; n=m gives identity scalar extension and the mate identity. For zero inputs all maps are the unique maps on zero. For E=Q_ell and n=1 the augmentation is the usual two-term pi-resolution; for n>m the proof still uses K-flat balancing rather than an invalid regularity claim over a quotient ring. Neither boundedness, completeness nor properness is used in any application. I checked that none of the cited tools has a dependency path back to this item. Every step is shorter than 2000 characters; no comparison lemma was hidden in a long step. All non-elementary inputs are existing cited node statements, with verbatim extracts in citations.json, and off-unit tools are declared in split_report.tool_uses.

## Unfinished work

None in the one-level stage-1 split. The existing unsplit tool nodes remain their own queue items; this delivery does not claim Lean formalization of them.
