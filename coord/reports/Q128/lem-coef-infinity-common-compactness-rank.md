# Stage-1 split: lem-coef-infinity-common-compactness-rank

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-common-compactness-rank.json`: statement; split into six steps, statement and statement dependencies unchanged. No Mathlib match for the quasicategorical assertion.
- `dag/nodes/sec-six-functors/lem-coef-infinity-sharp-accessibility-enlargement.json`: new statement-only prerequisite, unsplit; no Mathlib match. This is HTT Proposition 5.4.2.9 with its cardinal inequality written out.
- `citations.json`: one precise verbatim statement excerpt for each citation of each step.
- `report.md`: this report. `searches.jsonl` is the record produced by msearch.py; `write_split.py` is sandbox-only preparation code.

One new node, zero new Mathlib leaves. The existing Mathlib leaf `lem-coef-small-family-regular-bound` and existing split `lem-coef-compact-small-colimits` are reused.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the exact item id, common compactness/cardinal terminology, `IsAccessibleCategory`, `SharplyLT`, `isCardinalAccessibleCategory`, and sharp-cardinal terms. No project declaration states either this item or the new prerequisite. Ordinary compactification common-refinement declarations are unrelated. The upstream master sorry declarations are not used as proof evidence.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, HTT.pdf (April 9, 2017), Proposition 5.4.2.9 and preceding sharp-cardinal convention (printed pp. 425-426), Corollary 5.3.4.15 (printed p. 401), Proposition 5.4.2.2 (accessibility presentations), Definition A.2.6.3 and its following successor-power observation (printed p. 819), for the item and `lem-coef-infinity-sharp-accessibility-enlargement`. Read the IAS PDF online; it is not archived in literature/. No document was downloaded, and no SGA source is used. The item proof is accordingly marked agent-written: it assembles the cited online results with an explicit cardinal calculation.

## What changed and what was wrong

The item had a true statement but no proof. Its warning that an arbitrary larger regular cardinal need not preserve accessibility is essential. I retained it mathematically by choosing an explicit successor-power cardinal and citing the general sharp-enlargement theorem only after checking its inequality. No statement dispute or target change is needed.

The already existing `lem-coef-presentable-cardinal-enlargement` assumes presentability, so it cannot be applied to this merely accessible category. The ordinary-category `lem-coef-accessible-functor-presentability-ranks` also cannot supply a quasicategorical theorem. Neither is silently used.

The current main-20261015 ancestor proof is at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. I read its finite-coefficient mapping-complex adjunction paragraph and the older master node, together with the chapter and inherited unit `sk-prop-sf-biduality-general`. This is a foundational input below the reflector-accessibility split, not a replacement of the unit's duality route. The new node retains the exact nearest blueprint ancestor and inserts the current item at the head of its via list. This item is not the unit's key node; no realized fields are changed.

## Mathlib and duplicate searches

All fresh searches were run with `/home/ubuntu/weil-launcher-nt/msearch.py Q128 lem-coef-infinity-common-compactness-rank ...`, and the recorded query strings and results were copied from its log. Both statements were searched semantically in two phrasings, with Loogle, LeanSearch, and source grep. Every service used here answered; none was recorded as unavailable or misreported as a match.

I read `CategoryTheory/Presentable/LocallyPresentable.lean:35-115`, `CategoryTheory/Presentable/Basic.lean:155-188`, `CategoryTheory/Presentable/SharplyLT/Basic.lean`, and `SetTheory/Cardinal/HasCardinalLT.lean:199-211`. The first files work with ordinary Category instances and Type-valued coyoneda, not mapping spaces and coherent filtered colimits. Loogle's online index returns an ordinary theorem named `Cardinal.SharplyLT.isCardinalAccessibleCategory`; the pinned local SharplyLT file ends at line 268 without this theorem. Even its advertised ordinary theorem would not be a one-line specialization to this quasicategorical result. The Mathlib compactness monotonicity hits are likewise ordinary-category facts; step 5 supplies the direct definition argument for coherent mapping spaces.

Before creating the new node I searched the entire DAG by HTT references `5.4.2.9`, `5.3.4.15`, `A.2.6.3`, `5.4.2.8`, and by sharp/accessibility and compact-colimit concepts, and read the statements of the relevant candidates. Blueprint-wide `blueprint_refs.py search` queries included accessibility, accessible, sharply, cardinal, compactness, regular cardinal, and compact; no blueprint node states the new enlargement criterion or the item. `blueprint_refs.py ancestor` gives `prop-coef-integral-exceptional-adjoint`. No Stacks tag is claimed for an infinity-categorical theorem, so there are no same-Stacks-tag pairs to distinguish.

## Not duplicates

- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-infinity-common-compactness-rank: the new lemma is a criterion at specified cardinals satisfying a uniform exponential inequality; it neither chooses a common rank nor mentions prescribed objects. The item's presentation-size bound, cardinal construction, compactness monotonicity and compact-colimit argument remain in the item's own steps.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-presentable-cardinal-enlargement: the existing lemma assumes presentability and chooses ranks for a small set of arrow endpoints; it does not give the universal enlargement criterion for an arbitrary accessible category.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-infinity-compact-approximation: the existing lemma existentially chooses two ranks for a finite diagram of accessible categories and functors and then gives compact-source slices. It does not assert accessibility at each prescribed pair satisfying the sharpness inequality.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-accessible-diagram-presentations: the existing statement already assumes accessibility at both ranks and proves a functor-category theorem; it cannot supply the missing accessibility hypothesis.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-accessible-functor-presentability-ranks: the existing theorem is for locally presentable ordinary categories and accessible ordinary functors, with set-valued Hom; the new theorem concerns coherent mapping spaces in merely accessible quasicategories.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-accessible-monad-presentability: the existing theorem is an ordinary monad-algebra presentability assertion, not a quasicategorical accessibility-enlargement criterion.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-accessible-arrow-inverse-image: the existing statement concerns inverse images in ordinary locally presentable arrow categories, not rank enlargement for arbitrary accessible quasicategories.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-small-saturated-arrow-accessibility: the existing theorem is accessibility of a strongly saturated arrow subcategory in a presentable quasicategory; its statement gives no rank-enlargement criterion.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-infinity-reflector-accessibility: the existing theorem deduces accessibility of a reflector and its image; it gives neither the exponential criterion nor accessibility at a specified rank.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-accessible-subdiagram-criterion: the existing theorem concerns ordinary accessible full subcategories and approximation by subdiagrams, with local presentability of an ambient ordinary category.
- lem-coef-infinity-sharp-accessibility-enlargement vs lem-coef-compact-small-colimits: closure of compact objects under existing small colimits does not produce a small compact generating family at a new rank; both are needed in the proof.

## Review by Q128

I checked the statement and every step against the online HTT text, in particular the full statement and proof of Proposition 5.4.2.9 and the size hypothesis in Corollary 5.3.4.15. The new node is precisely the former proposition with lambda for its original rank and kappa for its enlarged rank. Its assumptions are infinite regular cardinals, strict inequality, the explicit exponential bound, and accessibility of the input quasicategory; no cocompleteness or presentability is assumed or needed. I also read Definition A.2.6.3 and the following successor-power example, rather than relying on an unverified assertion that accessibility is monotone. There is no matching Stacks tag, and no SGA source was consulted.

Step 1 uses the statement of `def-coef-presentable-infinity-category`, which actually defines accessibility through an essentially small compact generating family and small filtered presentations. Thus choosing a presentation for each prescribed object is an unpacking of that statement. I retained the precise generation clause in citations.json, not merely a quote that says a rank exists. The family of indices is small in the original universe, not just the larger universe.

Step 2 uses the full statement of `lem-coef-small-family-regular-bound`. Its inputs here are the small index set J with one added point, the sets of nondegenerate simplices of the chosen small quasicategories, and lambda's underlying small set at the added point. Its bound is therefore uniform in j and also bounds lambda. I verified its Mathlib match directly at HasCardinalLT.lean:201-206. The step does not assume a bound on a proper class of presentations.

Step 3 is the elementary cardinal construction, not a hidden theorem node. With a=2^theta, any set of size less than a^+ has size at most a; a union indexed by fewer than a^+ such sets has size at most a times a, proving regularity. The exponential inequality is explicitly calculated, and the step uses the definition node's nondegenerate-simplex convention for kappa-smallness. All these cardinals stay in the original universe. This avoids erroneously bounding only the vertices of I_j, or counting degenerate simplices against a finite bound.

Step 4 cites the new node's actual specified-cardinal criterion, together with the definition node's local-smallness and filtered-colimit clauses. The proof has already supplied every hypothesis, including the strict rank inequality and the exponential inequality. This is the only new non-elementary prerequisite. No proof of that node is supplied, as required for a new unsplit node.

Step 5 uses only the compactness and filteredness definitions. Every kappa-filtered category is lambda-filtered because every lambda-small test diagram is kappa-small. The lambda-compactness comparison for a generator is therefore exactly the desired comparison on each kappa-filtered diagram. This is compactness monotonicity, not the false unrestricted monotonicity of accessibility.

Step 6 uses the statement of `lem-coef-compact-small-colimits`, not its proof: it requires local smallness, all small kappa-filtered colimits, a kappa-small diagram of kappa-compact vertices, and the existence of that diagram's particular colimit. Step 4 supplies the first two, step 3 the size, step 5 the vertex compactness, and step 1 the colimit. I checked explicitly that this node requires neither all small colimits nor a filteredness hypothesis on the small diagram. Thus it applies to the original presentations even though their shapes need not be kappa-filtered.

For the new statement's edge cases I checked lambda=aleph_0 (the enlargement hypothesis is valid for uncountable successor-power kappa), the empty category (the accessibility assertion is vacuous where presentations have no objects), and ordinary nerves such as Set (ordinary presentability is consistent with the stated infinity-category result). For the item I checked J empty, one-object families, repeated objects, finite presentation shapes, and arbitrarily large but small shapes. Adding lambda at the extra index keeps the cardinal construction valid even for J empty. For the cardinal inequality nu=0 gives 1<kappa, including mu=0; the general bound covers all other cases. I did not assume an initial object in an empty category or in a merely accessible category.

Against delivery-errors B-E: the single new node introduces its objects and hypotheses, cites the actual definition nodes, contains only a statement and empty proof fields, and records real searches. Every non-elementary item input is a cited node, and the verbatim excerpts were checked as substrings of the cited statements. The new node is a general sharp-rank criterion, not a renamed common-family-rank assertion. The elementary size and compactness arguments remain in the item; existing generic results are reused rather than duplicated. The prerequisites do not depend on the item: the size-bound leaf and compact-colimit node have independent dependency paths, and the new node depends only on the two definitions. All proof uses are in proof_deps and conversely. There is no off-unit theorem tool use to declare: both existing result nodes share the item's unit. No live project, launcher source, Lean file or compiler was changed or run.

## What remains

The new enlargement criterion is deliberately unsplit for a later worker. This delivery ends after the required successful dry run; the second reader performs delivery.


## Second reading by Q128

- Item statement: checked against HTT Proposition 5.4.2.2(3), Proposition 5.4.2.9 and Corollary 5.3.4.15, and the actual universe/compactness definition nodes; PASS, the small-family consequence has the required common accessibility rank and no extra presentability assumption.
- Step 1: checked the full generation clause of `def-coef-presentable-infinity-category` against HTT Proposition 5.4.2.2(3); PASS, choosing a small filtered presentation for each member of the small family is precisely unpacking accessibility.
- Step 2: checked the entire statement of `lem-coef-small-family-regular-bound` and Mathlib `HasCardinalLT.exists_regular_cardinal` at HasCardinalLT.lean:199-206; PASS, the disjoint union over the small set with one extra point bounds lambda and every set of nondegenerate simplices.
- Step 3: checked HTT Definition A.2.6.3 and its successor-power observation (printed p. 819), the definition of kappa-smallness, and each cardinal calculation; PASS, fewer than a-successor summands have at most a elements each and at most a summands, and mu^nu is bounded by (2^theta)^theta = 2^theta < kappa.
- Step 4: checked the complete new node statement against HTT Proposition 5.4.2.9 and its preceding sharpness convention (printed pp. 425-426); PASS, both ranks are infinite regular, lambda < kappa, and every required exponential inequality was established before application. Accessibility supplies precisely local smallness and the filtered-colimit existence used later.
- Step 5: checked the filteredness and mapping-space compactness clauses of `def-coef-presentable-infinity-category` against HTT Definitions 5.3.1.7 and 5.3.4.5; PASS, every lambda-small test shape is kappa-small, so a kappa-filtered diagram is lambda-filtered and the same canonical compactness map is an equivalence.
- Step 6: checked the entire statement of `lem-coef-compact-small-colimits` against HTT Corollary 5.3.4.15 (printed p. 401); PASS, local smallness, all small kappa-filtered colimits, size of each shape, compactness of its vertices, and this particular colimit are supplied by steps 4, 3, 5 and 1 respectively. The chosen presentation need not itself be kappa-filtered.
- New node `lem-coef-infinity-sharp-accessibility-enlargement`: compared all hypotheses and the conclusion to HTT Proposition 5.4.2.9 with its relation explicitly expanded; PASS. Statement-only, self-contained through the two actual definition nodes, correct single TeX escaping, source by exact proposition/definition numbers (no corresponding Stacks tag), and strictly smaller than the item: it neither chooses a rank nor makes prescribed objects compact.

Edge cases checked independently: the empty family still bounds lambda via the extra point; the empty quasicategory is accessible at every rank and has no nonempty object family; in the nerve of Set the empty set and singleton are compact at every infinite regular rank and a set of size theta is compact at the chosen kappa > theta. For lambda = aleph_0 the criterion permits kappa = aleph_1; finite exponents of mu < aleph_1 stay countable. In the explicit construction, nu = 0 gives mu^0 = 1 < kappa even for mu = 0, and mu = 0 with positive nu gives 0 < kappa. No zero object, initial object, scheme, or nonempty family is assumed.

I independently searched the whole DAG by source numbers 5.4.2.9, 5.3.4.15 and A.2.6.3 and by sharpness/common-compactness/accessibility-rank language. I read the candidate statements of `lem-coef-infinity-compact-approximation`, `lem-coef-presentable-cardinal-enlargement`, `lem-coef-accessible-diagram-presentations`, the ordinary-category rank/criterion nodes, and the actual parent `lem-coef-infinity-reflector-accessibility`. None states the specified-cardinal criterion. The first chooses ranks existentially, the second assumes presentability, and the third assumes accessibility at both ranks. Fresh whole-blueprint searches for accessible and compactness found no duplicate; the latter's hits concern geometric constructible compactness. The ancestor command confirmed `prop-coef-integral-exceptional-adjoint`, and I read its current main-20261015 adjunction proof and the chapter/unit records. The cardinal argument serves the recorded foundational ancestry and changes no unit route.

My four fresh msearch calls used different phrasings and are retained verbatim in searches.jsonl: two LeanFinder queries, one Loogle query and one source grep. The Loogle sharp-accessibility hit was inspected as an ordinary Category theorem, and the pinned source's ordinary accessibility definition was read at LocallyPresentable.lean:36-51 and 84-101. No quasicategorical Mathlib leaf was found. A fresh read-only source search of slopmaster2/WeilConjectures, slopmaster2/Comparator and dag/lean_names_upstream.json by both ids and accessible/sharp/rank vocabulary found no exact project declaration. No upstream sorry was treated as a proof. No SGA source was used.

All seven original citation excerpts were checked as verbatim substrings of the cited statements. The existing dependency closure (249 nodes) has no path back to the item; the new node depends only on definitions. Both result nodes reused in the proof belong to the item's unit, and the size-bound node is already a Mathlib leaf. There is no new off-route tool use.

Changes made:

- Expanded the step 2, step 4 enlargement, and step 6 citation quotes to the full cited statements, so their hypotheses are visible alongside the conclusions; the statements needed no repair. Step 5 was subsequently rewritten in the updated definition's direct cocone-preservation language, as recorded below.
- Added the independent second-reader Mathlib searches to the appropriate nodes and preserved their actual tool log entries.
- Appended this second reading; retained every first-worker section, including `## Review by Q128`.

No statement dispute, node deletion, new node beyond the original one, new Mathlib leaf, or change to the mathematical claims was needed. Validation and delivery results follow below.

Required server dry run: `deliver.py Q128 lem-coef-infinity-common-compactness-rank --no-push` returned `OK (not pushed)` at `eda8f66e91`: preflight passed. The checks were run only by the delivery tool on the server, never locally. Proceeding with the required final delivery.

### Shared-definition update during delivery

The first final-delivery attempt stopped before pushing: the synchronized definition node `def-coef-presentable-infinity-category` had changed after the successful dry run, so step 5's old canonical-map quotation was no longer verbatim. I opened the updated shared node, which now defines compactness by preservation of every coherent colimiting cocone in the specified category of spaces. I replaced step 5's quote with that exact sentence and rewrote step 5 to apply lambda-compactness directly to an arbitrary kappa-filtered colimiting cocone. The same functor and same cocone are used at both ranks, so the argument requires no comparison theorem or added hypothesis. All seven citation quotes were rechecked against the current statements. The item and new-node statements remain unchanged. A new required dry run and final delivery follow this correction.

Corrected required dry run: `deliver.py Q128 lem-coef-infinity-common-compactness-rank --no-push` returned `OK (not pushed)` at `3117708eed`: preflight passed.
