## Worker report

Changed `dag/nodes/sec-six-functors-basics/lem-sfb-purity-etale-assassin-criterion.json`: corrected the special-fibre coverage hypothesis and supplied seven proof steps, their exact dependency union, proof origin, fresh Mathlib searches and blueprint correspondence. `citations.json` contains 32 verbatim statement quotations, one for each step/citation pair. No Lean was written, and no compiler or build tool was run. Only this sandbox was written.

## New nodes

None. In particular, a new Tag 05L3 node would duplicate a specialization of the existing, more general `lem-trf-flat-relative-associated-specialization` (Tag 0GSI). The argument choosing a component and its generic point is in step 4 and cites the existing component-coverage and scheme-sobriety statements.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, relative-assassin names, assassin, and pure-along names found no declaration stating this criterion. General cohomological purity declarations concern another notion and are not attachments.

## WANTED

None: the item, the elementary-neighbourhood definition, the flat-specialization input and the supporting geometric facts are available in the local Stacks sources.

## Source error

STATEMENT-DISPUTED: Tag 05L4 (`flat.tex`, `lemma-criterion`) really states the insufficient condition that `g(X')` contains the associated points of `F_s`. This is not merely an import transcription error. The first proof paragraph silently replaces the base by the selected elementary neighbourhood, which does not preserve that coverage assumption.

Explicit counterexample: let `S = X = Spec(k)`, `f = id`, and `F = O_X`, for any field k. Let `S' = Spec(k) coproduct Spec(k)`, let e be the fold map, and choose s' in its first component. Let `X' = Spec(k)`, let g be the identity onto X, and let p be the inclusion into the second component of S'. Then e is an elementary etale neighbourhood in the actual definition (`more-morphisms.tex`, `definition-etale-neighbourhood`): it is etale and the residue extension at s' is the identity. The definition does not say that the rest of the fibre of e is empty. Both f and p are finite type, F is flat, g is etale, and g(X') contains the unique associated point of X_s. G = g*F is pure along the empty fibre X'_{s'}: no point above a generalization of s' lies in the other open-and-closed component, even after an elementary neighbourhood base change. F is pure over the one-point field base. Nevertheless Y = S', F_Y = O_{S'}, and h(X') is just the second component, so it misses the associated point above s' itself. The asserted right-hand condition is false.

Correction: replace `g(X') contains Ass_{X_s}(F_s)` by `g(X'_{s'}) contains Ass_{X_s}(F_s)`. Here X'_{s'} is the fibre of p, not the full inverse image of X_s under g. Because kappa(s') = kappa(s), this is exactly coverage of the associated points of the selected special fibre Y_{s'} by h. This is the hypothesis the source's first reduction needs. All other hypotheses and the complete equivalence are retained. The report explicitly records the added restriction; it is not represented as a verbatim theorem of the erroneous source.

The proof is marked agent-written: it retains the source's open-image, flat-specialization, relative-assassin-base-change and chart-specialization argument, but tests every elementary neighbourhood directly instead of invoking the henselization criterion. This avoids an unrecorded henselization theorem and its further permanence requirements.

### Effect on existing callers

The entire DAG search found one citer: `lem-sfb-flat-fp-purity-open`.

- Its step 4 is not justified by the corrected statement as currently written (holds: false for that invocation): its step 1 only quotes `lem-sfb-flat-fibre-projective-etale-cover` for X_s contained in g(X'), not coverage by X'_{s'}. The stronger chart coverage must be established from the chart construction, or a different valid argument supplied, before that invocation can be used. The statement of the openness theorem itself is not refuted by this example. I have not edited the caller or its chart node.
- Its step 6 uses the identity neighbourhood on S' and h as the chart. There, coverage of fibre associated points by h(X') is the same as coverage by the chart fibre over the selected point, so this invocation remains valid.

This correction and the outstanding caller obligation are submitted for independent maintainer review as instructed by the statement-dispute rule.

## Searches and blueprint

Read the latest blueprint's `sec-six-functors-basics/_section.md`, the unit `_section.md` and `sk-thm-sf-ctf-stability.proof.md`. The inherited support chain belongs to paragraph 3, preservation by direct image via compactification. The existing chapter/unit JSON records were read too; no unit or chapter was changed. The item is a supporting Stacks lemma far below this route, not a replacement of a unit step. `tools/blueprint_refs.py ancestor` returns `None` for this inherited created-item chain; its recorded `from.place` already describes the full chain, and I retained the existing ancestor/via data. The whole-blueprint searches `purity`, `05L3`, `relative assassin`, and `purity etale` did not find an equivalent imported criterion (the purity hits concern cohomological or weight purity).

Fresh msearch.py calls, in `searches.jsonl`, used two semantic phrasings, LeanSearch, Loogle and source grep. The relative-purity phrasing returned etale loci, the scheme etale site and spreading-out declarations. The specialization phrasing returned flat going-down/generalizing maps and structure-sheaf stalkSpecializes formulas; these have no relative-assassin or purity conclusion. Loogle (`"Associated", "Etale"`) and the relative-assassin/pure-along grep returned no hits. The existing imported search records were retained. None of these hits states the item or a one-line specialization of it.

## Not duplicates

No new nodes are proposed. The exact and general existing statements were read rather than restated: notably Tag 0GSI for the specialization part of 05L3, Tag 05DC for image containment under base change, and the existing locally-Noetherian etale associated-point invariance for the fibre argument.

## Review by NN

I read the statement and all three proof paragraphs of `flat.tex` Tag 05L4, the actual elementary-neighbourhood definition in `more-morphisms.tex`, Tag 05J4's purity definition, Tag 05J9's descent statement, the full statement of Tag 0GSI, and Tag 05DC with its following base-change remark. There are no new nodes requiring an additional source review. The two-copy example forced the correction above before writing the split. It also explains precisely why merely repeating the source's first reduction would give a false proof.

Step 1 uses the existing finite-type composition/base-change statement only for base change; the two module-pullback statements give finite type and quasi-coherence; the actual pullback-composition isomorphism gives h*F_Y = G. Etale base change gives the projection Y -> X etale, cancellation applies to that projection and its composite g, and etale openness then gives W open. Each cited statement says this. Fibre identification uses the residue-field isomorphism in the elementary-neighbourhood definition; coverage is taken from the corrected hypothesis, not from the image of all of X'.

Step 2 uses the actual stalk formula together with `lem-pc-pullback-stalk-relative-flat-extension`. I checked that the latter is pointwise and needs only flatness of F_x over the local base ring. I did not substitute the global relatively-flat pullback theorem, whose global flatness hypothesis is absent. Points in Y_{s'} map into X_s, so exactly the given flatness hypothesis is available.

Step 3 proves elementary-neighbourhood ascent by composition: etaleness is supplied by the composition statement and residue-field isomorphisms compose. The sheaf identification is the existing pullback-composition isomorphism. Descent is supplied by `lem-sfb-purity-flat-point-descent`, whose finite-type, finite-type quasi-coherence and flatness-at-s' hypotheses hold. Etale implies flat by the definition node, not by an unstated property.

Step 4 uses the purity definition with the identity elementary neighbourhood, then the reduced-induced-closed-subscheme existence statement for the closure of a. Irreducibility is written out. The component-coverage statement gives a component of its nonempty fibre, and scheme sobriety gives that component's generic point. The Tag 0GSI node is applied with q, F_Y and that component; its actual statement gives the associated-point conclusion at its generic point under flatness at that point, already checked in step 2. The relative-assassin definition then identifies it with a special-fibre associated point. Generalization stability of an open is elementary from the definition of closure. No universal purity assumption is inserted.

Step 5 takes only the upstairs-to-downstairs implication from the actual Tag 05DC node. It does not claim inverse-image equality for arbitrary base change. The actual base-change-image node, not just the universal property of a fibre product, supplies the lift b of a through the base-changed chart. Continuity carries u -> t to a generalization of s', so the assumed containment applies.

Step 6 checks the missing hypothesis that often invalidates an etale-assassin citation: both fibres are locally Noetherian. Finite-type base change gives finite type over the field kappa(u); fields are Noetherian by their two ideals; `pqf-lem-locnoeth-lft` gives local Noetherianity. Etale base change gives the fibre map etale. Pullback composition identifies its pulled-back sheaf with G_T on the fibre, and quasi-coherence is supplied by the module-pullback theorem. Thus the exact statement of `lem-sfb-scheme-etale-assassin-invariance` applies, with no Noetherian assumption on either entire base scheme.

Step 7 uses purity of G in its defining elementary-neighbourhood form. The relative associated point b from step 6 must specialize into the fibre at t; continuity of h_T carries that specialization to one for a. This rules out every impurity in every elementary neighbourhood of s', which is precisely purity of F_Y. Step 3 then gives purity of F. This is an argument, not a new node carrying the conclusion.

Small cases checked: zero F gives empty associated sets and both purity conditions; over a field the only generalization is the chosen point and the corrected coverage hypothesis gives the right-hand condition; an identity base neighbourhood makes the corrected coverage assumption equivalent to its usual fibrewise formulation. Empty special fibres were checked with a DVR base and X = D(pi), F = O_X, and an empty chart: the generic associated point escapes the closed fibre, so purity and the required containment both fail. The two-component counterexample tests the distinguished-fibre issue explicitly. No step exceeds 2000 characters. The off-unit specialization, relative-assassin and point-image results are declared as generic tools in split_report, with their exact purposes, rather than silently replacing the unit route.

The content checks B--E found no proposed new-node duplication, hollow notion, hidden theorem cited only by a tag, or clause moved to a replacement node. Every cited statement has been opened and copied verbatim into citations.json. The mathematical correction and sole caller obligation are the material limitations of this delivery; nothing else remains unfinished in this item's corrected split.
