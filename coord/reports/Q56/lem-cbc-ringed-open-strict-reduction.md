# Stage-1 delivery: lem-cbc-ringed-open-strict-reduction

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-ringed-open-strict-reduction.json: existing statement split in six steps; Mathlib verdict no match; statement and statement dependencies unchanged.
- citations.json: 27 step/node entries, each with a verbatim statement excerpt.
- searches.jsonl: actual msearch.py output log; inherited item searches retained in the node and six searches from this attempt appended exactly as logged.
- report.md: this report. write_split.py is a sandbox-only authoring script.

No new nodes, no new definitions, no Mathlib leaves. No unit or chapter record changed: the item is a refinement below the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures for the exact item id and for ringed open extension, strict reduction, reduction towers and extension/tensor terminology. The project has no declaration stating all clauses. The existing completedUpperStarOpenImmersionLowerShriekIso in SixFunctors/ProEtale/FiniteCoefficient/Derived/CompletedExchangeComparison.lean is a different assertion, over constant R coefficients, with an additionally completed target and a principal regular ideal; it is not this strict completed-ring reduction comparison. The topological-space tensorTotal_extend_natural_iso is a different operation (extension of complex degree indices) and does not attach.

## WANTED

None. The source documents used are available locally.

## Problems found and changes

The item was unsplit, with no proof. Its statement is correct and retained. I replaced no hypotheses, coefficient categories or conclusions. The blueprint's opening sentence that reductions commute with extension by zero needs a ringed tensor argument in addition to exactness. The split supplies this on a single flat-term K-flat representative and retains the strict transition and augmentation maps. It never claims that a family of derived evaluations determines a tower morphism.

I distinguished the coefficient ring P_b=A/I^b from the reduction complex Q_b=P tensor (P_b)_W to avoid a type ambiguity. The scalar-action comparison is before restriction of scalars, and the normalization is computed over the intermediate quotient ring, where Q_b and its extension are K-flat. I did not assert that Q_b is K-flat over A_W.

Mathlib searches returned ordinary algebraic tensor/quotient formulas, Zariski module presentations, presheaf tensor definitions and generic zero-object facts. None gives the strict sheaf tower comparison. One Loogle query failed on an unknown identifier and is explicitly recorded as invalid, not as evidence of absence; the subsequent quoted-name query was valid. Both LeanFinder phrasings were read. No searches are invented or rewritten from memory.

## Unfinished

Nothing remains in this one-level split. The reused unsplit flat-resolution node stays a separate existing item, as required; this delivery does not edit or split it.

## Not duplicates

There are no new-node/existing-node pairs. The searches by Stacks tags 0E8I and 0GL1, blueprint searches for reduction tower / extension tensor / 0E8I, and DAG and source searches led to reuse of the existing tensor, flat-resolution, coefficient normalization and localization nodes. In particular the item does not duplicate lem-sf-integral-open-reduction-comparison: that theorem assumes complete DVR coefficient objects and quasi-compact opens and includes realization/completeness, whereas this item treats arbitrary K and arbitrary open e, together with its strict augmentation and full quotient normalization. That larger theorem was not cited, since its dependency route goes through the parent completed comparison.

## Review by Q56

I read coord/brief-stage1.md, stages/1-dag.md, the three blueprint levels in SETUP.md, GOAL.md, roles/worker.md, the unit sk-prop-sf-cbc and chapter sec-smooth-purity records, and delivery-errors B through E. I checked the item against the opening paragraph of main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md. I read Stacks sites-modules.tex, lemma-j-shriek-and-tensor (0E8I), including its five Hom bijections, and sites-cohomology.tex, lemma-j-shriek-and-tensor (0GL1), whose derived proof omits the resolution details. The strict augmentation and quotient refinements are an agent-written expansion, marked accordingly. There are no new nodes requiring separate source reviews.

For Step 1 I opened the statements of lem-weil-proetale-weakly-etale-localization and lem-weil-pbc-profinite-coefficient-inverse-image. The former gives the slice equivalence and subterminal nature of the open, and the latter explicitly gives completed and finite coefficient identifications commuting with projections and transitions. This avoids using the constant-sheaf clause alone for the completed ring. The finite rings and small pro-etale sites are supplied by the datum. I read lem-pur-site-restriction-module-adjunction-exact (exact module extension on an arbitrary slice), lem-pc-kflat-resolution (flat terms and termwise surjectivity), lem-cbc-ringed-open-flat-resolution (preservation of all those properties), lem-weil-tower-category-levelwise-abelian (levelwise kernels/cokernels), and lem-sf-exact-functor-derived-triangulated (termwise derived functor). Each says the property used. No quasi-compactness is hidden in any of these hypotheses.

For Step 2 I read lem-weil-pbc-ringed-slice-extension-tensor and lem-sf-open-tensor-normalization, not merely their proofs. The former states the natural sheaf tensor isomorphism; the latter fixes the inverse of the derived tensor comparison as the open-unit adjunct and fixes that unit to be the same section. Flat G and JG concentrated in degree zero are K-flat because their tensor functors are exact. Thus the derived formula computes the ordinary sheaf tensor map. This pins the actual inverse on a summand to [g tensor b] -> [g] tensor b, whose inverse is the map in the item. I checked balancing, restrictions, differential naturality, and extension of the identities through the universal properties in def-pur-sheaf-tensor-product, def-weil-extension-by-zero-presheaf and def-weil-presheaf-modules-sheafification. I used the normalization theorem as an existing generic tensor tool, rather than asserting that an unspecified tensor isomorphism has the required formula.

Step 3 is the explicit transition equality and scalar calculation. I reread the adic datum's q maps and strict tower definition, def-pc-sheaf-restrict-scalars, and the uniqueness of the module action in the sheafification definition. They justify treating the same comparison first as a quotient-module map, then as an A_T-module map. Step 4 uses precisely the extension summands and sheafification universal property: both augmentations send [p] to [p tensor 1]. These two steps are elementary calculations, not new lemmas and not citations of a definition as though it were an exactness theorem.

For Step 5 I read lem-pur-kflat-change-of-rings, which gives flat-term K-flatness over the quotient ring, and reapplied the existing flat-resolution theorem with that quotient ring. The adic datum's statement itself gives the normalization formula, its inverse, unit and three-index cocycle. I checked that both paths send (([p] tensor r) tensor s) to [p tensor q(r)s]; for three quotients the result is [p tensor q(r)q(s)t]. This is a calculation of actual maps, not an assertion that coherence automatically transports. No object is assumed flat over the wrong coefficient ring.

For Step 6 I read lem-pur-derived-change-of-rings (1), lem-weil-tower-category-levelwise-abelian, lem-weil-pbc-site-derived-tensor-descent and lem-weil-pbc-localization-universal-property. The first preserves quasi-isomorphisms between the K-flat representatives; levelwise cohomology applies to actual tower complexes; the descent theorem's first assertion is exactly the equivalence from localized flat-term K-flat representatives to D(R); and the localization theorem descends natural transformations and their inverses. The comparison is constructed before localization and respects chain maps and homotopies. Thus naturality and resolution independence concern the strict derived tower morphism itself. The earlier strict equalities survive under the functors.

I checked the dependency statements for routes back to the item: none has one, including the normalized tensor theorem. The off-unit citations in split_report.tool_uses are generic coefficient, tensor, resolution and localization tools; they support the blueprint's tensor/reduction inference and do not replace its route. I added no maintainer-owned top-level tool_uses.

Small cases checked: identity open (the ordinary tensor identity); empty open and empty scheme (zero complexes); zero coefficient ring and I=A (all quotients zero); I=0 (identity quotient transitions); K=0; b=a (tensor unit); c=b=a (unit cocycle); and genuinely derived reduction such as Z_l with K=Z/l. The last case stresses that quotient levels need not be A-flat, while they are modeled by complexes K-flat over the quotient for successive normalization. Unbounded P causes no tensor-totalization sum issue here because each quotient coefficient complex is concentrated in degree zero. Completeness, constructibility, quasi-compactness and regularity of e were never used.

Against B: no new nodes, malformed statements, false leaf claims or unrun searches. Against C: every non-elementary ingredient is an explicit cited statement, with quotations in citations.json; all dependencies exist, none is a pointer to an unquoted construction, and no cycles arise. Against D: the six steps do the actual argument and no node merely renames a clause. Against E: all coefficient rings, strict maps, normalization domains and compatibility formulas were checked as described. Every proof step is below 2000 characters, and the only elementary steps are the displayed transition/scalar and augmentation calculations.

Server checks before packaging: srvcheck check_dag reported no finding introduced by the sandbox; srvcheck review_split returned PASS with 0 new nodes. The report will be followed by the required deliver.py --no-push and direct delivery.

The first deliver.py dry run stopped before packaging because the restriction-of-scalars quote was under 40 characters. I replaced that excerpt with the complete verbatim statement; no proof or dependency repair was needed.
