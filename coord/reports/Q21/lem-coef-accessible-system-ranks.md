# Stage-1 report: lem-coef-accessible-system-ranks

Group Q21; 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-accessible-system-ranks.json`: existing item, split into ten proof steps; no installed Mathlib match.
- `citations.json`: thirteen verbatim quotations, one for every cited node use.
- `searches.jsonl`: searches recorded by the required msearch command.

No new DAG nodes or Mathlib leaves. The inherited sandbox had already removed two draft eventual-rank nodes which hid the main argument.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, accessible, uniformization, strongly accessible, and presentability-rank terminology found no project declaration stating all clauses.

## WANTED

WANTED: Adámek--Rosický, *Locally Presentable and Accessible Categories*, Theorem 2.11 and Uniformization Theorem 2.19, for the full textbook proof behind this item. The proof delivered here is agent-written.

Beke--Rosický, *Abstract elementary classes and accessible categories*, §§2--3, and Brooke--Taylor--Rosický, *Accessible images revisited*, §2, were read online at the URLs recorded in the item's source; neither was downloaded into the repository. No Stacks tag was identified for this uniformization theorem, and no SGA source is used.

## Corrections and unfinished work

The shared statement already has the correct small-family wording; its statement is retained verbatim. The inherited report described two deleted nodes, a five-step proof and six quotations. I replaced that stale report with this account of the actual ten-step split and thirteen quotations. The draft eventual-rank nodes remain removed, since they would transfer the principal clauses into new nodes (D1/D2). No mathematical work remains before the second reader; delivery is deliberately left to that reader.

## Not duplicates

No new nodes are proposed. I compared the item with `lem-coef-accessible-functor-presentability-ranks`, `lem-coef-locally-presentable-rank-enlargement`, `lem-coef-ordinary-presentables-small`, and the infinity-category rank lemmas. The first three use locally presentable hypotheses or address smaller conclusions; the infinity-category nodes concern different objects. Supporting ordinary-category facts already exist and are cited. Whole-DAG and blueprint searches by accessible, uniformization, presentability ranks, and the item id found no existing node stating the simultaneous system-rank conclusion.

## Review by Q21

I read the shared item, the six-functors chapter record, the unit record `sk-prop-sf-biduality-general`, the current main-20261015 blueprint ancestor `prop-coef-integral-exceptional-adjoint.proof.md`, and the parent accessible PIE-closure node. The ancestor's second paragraph treats derived coefficient adjunction; it does not itself state or prove this cardinal lemma. This is the inherited auxiliary ordinary-category uniformization input to the PIE/monad route, so its expanded argument is correctly marked agent-written. I read Beke--Rosický §2, printed pp. 2--4 (accessible categories and their nonmonotone rank spectrum), §3, printed pp. 5--6 (uniformization and sharp upper ranks), and Brooke--Taylor--Rosický §2, printed p. 3 (sharp ranks and strong accessibility). Their conventions use directed posets; Step 2's existing reindexing lemma bridges the filtered-category convention here. The power bound in this proof is sufficient for the sharp-subset lemma; no equivalence with weaker definitions of sharply less than is assumed. The source's stronger convention for an accessible functor is reached in Step 6 before controlling images.

Step 1 quantifies the category, its accessibility rank nu, generators, and the upper power-bound rank tau. It merely introduces the construction proved in Steps 2--5 and invokes no uncited rank theorem.

Step 2 cites `lem-coef-cardinal-filtered-poset-reindex` for the small nu-filtered poset and preservation of the original colimit cocone, and `lem-coef-sharp-filtered-poset-subsets` for the covering tau-filtered poset B. I opened both statements: they give exactly these conclusions, with nu<tau, both ranks infinite regular, and the power hypothesis of Step 1. The full-subposet arrow bound and passage from upper bounds to cocones are elementary; endpoints of every arrow are contained in a common member of B.

Step 3 cites `lem-coef-ordinary-small-colimit-presentable`. Its statement requires existence only of the particular colimit, an indexing arrow bound, and presentability of the values; it does not require cocompleteness. Each restricted diagram is nu-filtered, so its colimit exists. Each value is tau-presentable because a tau-filtered diagram is nu-filtered. The arrow bound was established in Step 2.

Step 4 cites `def-weil-pbc-category-colimit` for its universal property. I checked the explicit cocone gluing: a common member establishes independence of the representative containing an object, and a member containing an arrow establishes naturality. Conversely every cocone restricts to the subdiagrams, so the two constructions are inverse. I checked the encoding on cardinals delta<tau: a small family of generators and its small Hom sets yield a small full category; the set of all relabelled posets and diagrams is small. This yields a fixed small generator family, rather than an object-dependent one. These are elementary universal-property and set arguments.

Step 5 cites clause (1) of `lem-weil-pbc-filtered-colimit-sets-elementwise`. I read the statement: every element of the colimit of a small filtered diagram of sets comes from one stage. Here B is small, nonempty and tau-filtered, hence filtered. Applying this to the inverse image of the identity under the presentability comparison gives s with rs=1, exactly the retract claim.

Step 6 cites `lem-coef-small-family-regular-bound` and `lem-coef-infinite-cardinal-successor-regular`. I checked the former bounds the disjoint union of the witness sets, not just their number, and the latter applies to the infinite power cardinal. The cardinal-power calculation supplies Step 1's hypothesis at beta. Each beta-filtered diagram is also alpha_t-filtered, so the functor preservation hypothesis applies. Thus a common category accessibility rank is proved before it is used.

Step 7 cites the regular-bound node and the ordinary small-colimit-presentability node. The beta-accessible presentation of each image of a generator has a small arrow set. Choosing mu larger than beta and that arrow set makes all its values mu-presentable by the definition, and the cited small-colimit node proves that its colimit is mu-presentable. This argument uses no locally-presentable-only object-rank theorem.

Step 8 cites the same bound and small-colimit nodes and the successor-regularity node. The pair set (t,g) is small, so their image-rank sets have a common bound eta; the additional beta and b sets cover empty families. Kappa=(2^eta)^+ satisfies the power inequality. Steps 1--5 give the beta-filtered retract presentation; Step 6 makes its image colimiting, and the image-rank and arrow bounds justify the small-colimit lemma in the target.

Step 9 cites the colimit definition for inducing maps on Hom-set colimits. I checked the explicit natural splitting i_Z(f)=fv, p_Z(g)=gu, and both composites of the proposed inverse p c_D^{-1} i_Z. This proves presentability of the retract in a few lines, without an unproved transport assertion.

Step 10 uses the preceding proved conclusions only. Lambda=beta, beta<eta<kappa and b<eta give the required inequalities, existence and preservation of both types of filtered colimits, and preservation of kappa-presentable objects. Proving a stronger lambda-accessibility property does not change the statement.

I checked small cases: S empty forces T empty; T empty removes all image ranks; an empty accessible category gives vacuous object assertions and only filtered colimits; a terminal category and its identity functor satisfy every step. Generator families may be empty. All upper-bound conventions include the empty subset. Exponent zero, base zero, and finite b are covered by the infinite power bound. No arbitrary colimits or local presentability are assumed.

For B--E of delivery-errors: no new statement-only nodes need form or duplication checks; inline definitions make the item self-contained; no mathematical statement change is delivered. Every non-elementary input is an existing cited statement, and every citation was read against its hypotheses (C1/C4). The proof carries the enlargement, image bounds and retract argument itself (D1/D2). The small-category, small-Hom, regularity, filteredness and particular-colimit hypotheses are checked above. All non-leaf proof inputs have the same unit; remaining inputs are Mathlib leaves, so no off-unit tool use is needed.

I reran LeanFinder, Loogle, source grep and LeanSearch through msearch.py, with further phrasings after inspecting the inherited searches. Online Loogle advertises `Mathlib.CategoryTheory.Presentable.Uniformization`, but that module is absent from the pinned installed source. I read the actual accessible-category and presentability declarations and the pinned supporting leaf sources; individual witnesses or monotonicity do not give this simultaneous strong-rank conclusion. No false Mathlib match was recorded. No new nodes require per-node searches.

## Second reading by Q21

- Item statement: checked against the cited blueprint paragraph and its accessible-category definitions; verdict: retained, with the small-family quantifiers, arbitrary prescribed bound `b`, lower rank only for colimits, and upper strong rank all present.
- Step 1: checked against the item statement and the stated rank-enlargement construction; verdict: elementary setup, with no hidden arbitrary-colimit assumption.
- Step 2: checked against `lem-coef-cardinal-filtered-poset-reindex` and `lem-coef-sharp-filtered-poset-subsets`; verdict: hypotheses `nu < tau`, power bound, filteredness, coverage of objects and arrows, and the empty subset are used correctly.
- Step 3: checked against `lem-coef-ordinary-small-colimit-presentable`; verdict: each restricted diagram is `nu`-filtered, has fewer than `tau` arrows, and its values are `tau`-presentable, so the cited conclusion applies.
- Step 4: checked against `def-weil-pbc-category-colimit`; verdict: the gluing, independence, naturality, converse, and small relabelled generator-family arguments explicitly establish the required colimit and accessibility.
- Step 5: checked against clause (1) of `lem-weil-pbc-filtered-colimit-sets-elementwise`; verdict: the identity preimage yields the stated retraction with the correct orientation.
- Step 6: checked against `lem-coef-small-family-regular-bound` and `lem-coef-infinite-cardinal-successor-regular`; verdict: all category and functor witnesses, including empty families and the prescribed `b`, are bounded before choosing `beta`, and the exponent calculation is valid.
- Step 7: checked against the same regular-bound node and `lem-coef-ordinary-small-colimit-presentable`; verdict: each generator image receives an individual presentability rank without assuming local presentability or cocompleteness.
- Step 8: checked against the regular-bound, successor-regularity, and small-colimit nodes; verdict: the pair-indexed image ranks, `beta`, and `b` are jointly bounded, and the retract presentation plus preservation gives a `kappa`-presentable image.
- Step 9: checked against `def-weil-pbc-category-colimit`; verdict: the Hom-set splitting has `vu = 1`, both comparison maps are natural, and the displayed inverse proves presentability of the retract.
- Step 10: checked against the item conclusion; verdict: `lambda = beta < kappa`, `b < kappa`, all required filtered-colimit preservation and `kappa`-presentability clauses follow, including empty families.
- New nodes: none; no node-form, duplicate, or per-node Mathlib-leaf repair was applicable.

Changes made: none to statements, proof steps, citations, or searches; this second reading records the checks above and found no repair necessary.
