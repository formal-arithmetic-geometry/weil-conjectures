# Stage-1 report: lem-sfb-snc-tame-finite-fibre-classification

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-snc-tame-finite-fibre-classification.json`: item, statement unchanged, split into 12 proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-snc-tame-root-etale-extension.json`: one new statement-only unsplit node; no Mathlib match.
- `citations.json`: every step/node pair, with a verbatim statement quotation.
- `searches.jsonl`: actual msearch output records, retained in the sandbox. `write_split.py` is the sandbox-only preparation script; it is not part of the delivery.

There are **1 new node and 0 Mathlib leaves**. No Lean was written and no compiler, Lake, build, git, or local DAG/preflight check was run. The repository and launcher were only read; the required delivery tools handle their own staging.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for tame finite fibres, normal crossings and Kummer covers. The KummerTorsor, KummerCover, GaloisEvaluation, and trait-chart modules do not state the item's universal-residual SNC finite-fibre classification. Their Kummer constructions do not prove the required simultaneous root extension and residual splitting. The existing finite-locally-constant/finite-etale declaration in HenselianFiniteEtale.lean is an existing generic input, not an attachment for this item. I also searched `lean/Sheaf/` for the item and tame SNC content.

## WANTED

None. The relevant ILO, Bhatt–Scholze, Stacks and current blueprint sources are available locally.

## Findings and corrections

The item arrived with an empty proof. Its statement and every inherited metadata field are retained. I made no statement correction and found no statement dispute.

A local strict-henselian root description alone does not say that an arbitrary finite cover over the residual limit is split. Step 4 supplies the extra finite-stage argument: descend to a finite residual stage, regard the composite as a finite etale cover of the original stratum, and use the natural splitting of both that composite and the stage cover. Selecting the pointed stage summand then splits the original cover over the limit.

Likewise the finite root algebra modulo the old boundary ideal is not the residual ring: it is a nilpotent root thickening. Steps 5–6 explicitly remove this thickening before using the universal residual splitting, and lift the resulting isomorphism through two henselian pairs. They do not apply a local-ring theorem to the generally nonlocal ring H, or impose Noetherianity on its filtered colimit.

The frame argument in Step 2 uses the sheaf of all finite cardinality frames. This handles varying ranks without invoking an uncited openness theorem for fpqc type loci. The descent arrow in Step 9 is obtained at a finite root level and pulled back to the whole profinite overlap. It is not inferred merely from pointwise equalities. Its apparent reversed order from the convention (x,g) -> (x,gx) is checked explicitly; the root group is abelian, so the resulting permutations commute and give the asserted left action.

## Blueprint route and tool uses

I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sf-ctf-stability.json`, and the current main-20261015 `sk-thm-sf-ctf-stability-direct-images.md` and `.proof.md`. This item is below paragraph (3), the open direct-image input through open coefficient comparison. Its finite-cover argument supplies the already-selected tame root-tower extension branch; it does not replace that direct-image route. It is not the unit's key node, so no realization file is changed.

The inherited `blueprint.from.node` is null. The mandatory `blueprint_refs.py ancestor` command also returns None: the ancestor chain of created nodes does not reach an imported blueprint_kind record. I preserve that field and its via list, record the actual current paragraph in split_report, and give the new node the computed null ancestor with the item prepended to via. Its exact place is the finite-root etale normalization input. Blueprint searches for tame, tame ramification, normal crossings, Kummer, root, finite locally constant, and locally constant sheaves of sets found no duplicate of the item or the new extension statement. The existing finite-cover equivalence is reused.

Off-unit proof inputs are generic classical comparison, finite-cover, henselian, ring and topology tools. Any which are neither Mathlib nor recorded Lean-closed are declared in split_report.tool_uses with their role. None supplies an alternative finiteness or purity route. In particular no SGA source is cited or used; the geometric input is ILO IX, and the sheaf comparison is Bhatt–Scholze and Stacks.

## Mathlib searches

The new root-extension node has five actual msearch searches: two LeanFinder phrasings, a Loogle query, a LeanSearch query and a source grep. I read each returned hit. Loogle and grep returned zero matches. The semantic results give standard-etale presentations and etale algebra localizations (including Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial and Algebra.exists_etale_of_isEtaleAt), field Kummer extension formulas, and number-field ramification identities. These neither construct a tame normalization over an SNC scheme nor extend it etale after simultaneous roots. Thus this node is unsplit, not a Mathlib leaf.

I also searched the item and the finite set-site comparison while determining which existing inputs suffice. The hits include fully faithful condensed constant functors, generic sheaf congruences, and a faithful abstract Galois fibre functor. They do not give this geometric fully faithful finite-inertia classification. Those actual searches are also retained; no unavailable service is described as a mathematical negative result, and no unrun search is recorded.

## Not duplicates

lem-sfb-snc-tame-root-etale-extension vs lem-sfb-snc-tame-finite-fibre-classification: the new node constructs an etale extension over one finite root chart over the original Noetherian base; it has no residual universal cover, no fibre classification, no monodromy, and no normalized trivialization. The item explicitly makes no extension-across-boundary assertion. The item still proves its conclusions in the residual splitting and descent steps.

lem-sfb-snc-tame-root-etale-extension vs lem-per-prime-to-order-snc-kummer-charts: the latter requires a connected G-torsor of globally invertible group order and a given finite normalization, and concludes logarithmic local charts. The new node permits finite tame covers of arbitrary total degree, including degree divisible by p, and gives an ordinary finite-etale extension on a simultaneous finite root chart. The invertible-order theorem cannot be applied to the permutation group of an arbitrary finite tame cover.

lem-sfb-snc-tame-root-etale-extension vs lem-per-snc-root-punctured-torsor-splitting: the latter concerns an invertible-order torsor over a strictly henselian regular local ring and concludes punctured splitting. The new node concerns the original finite-type affine base, arbitrary tame finite covers, and a finite-etale model on a finite root chart; horizontal monodromy may remain.

lem-sfb-snc-tame-root-etale-extension vs lem-per-kummer-strict-local-standard-model: that node starts with a finite Kummer etale logarithmic cover and describes its strict-local standard form; it does not extend the given ordinary finite etale cover across the divisor or produce a single global finite root level.

lem-sfb-snc-tame-root-etale-extension vs lem-sfb-snc-universal-residual-charts: the existing node constructs residual neighborhoods and records root-algebra geometry and covering properties, but contains no extension theorem for a supplied finite tame cover. It is reused for exactly its geometry conclusions.

## Review by NZ

I checked the work against delivery-errors B through E, reading the statements of all cited nodes and the source passages alongside the proof. The new node introduces its field, ring, divisor, finite etale cover, each strict-local tower and the finite root chart explicitly. Its statement has no proof sketch and no dependency on the item, no unspecified normalization finiteness hypothesis, and no artificial prime-to-p degree restriction. ILO IX Proposition 2.1(i)–(iii), printed pp.133–134 (PDF pages 139–140), is the source I read for both the item geometry and this new node. The local quotient formula there is the simultaneous-root input; its etale-local extension statement gives the root-level unramified model. A common multiple of the finitely many local tame exponents gives the global n over the quasi-compact finite-type chart. The new node leaves this substantive geometric argument for its own later split, without moving the residual or categorical content out of this item.

For Step 1 I read the entire universal-residual-charts statement: it explicitly supplies henselianity, identification with the residual pointed limit, connected punctured finite and infinite levels, and the pro-etale covering. It is valid for the same chart and residual system used here; I do not use its source or its proof as an unstated theorem.

For Step 2 I read Bhatt–Scholze Lemmas 5.1.2 and 5.1.4 and Corollary 5.1.5, pp.34–35, together with the locally-classical-etale-cover, classical-sheaves and finite-cover-equivalence node statements. The first node explicitly gives etale sections of a locally classical sheaf that is locally nonempty. The finite-frame sheaf has this property, including cardinality zero, so the conclusion really gives etale finite frames. The finite-cover equivalence supplies both representability and compatibility with fibres and pullback; I did not cite a merely fully faithful Yoneda assertion as an existence theorem.

For Step 3 the new node supplies exactly the finite etale model and its punctured isomorphism. Its hypotheses are those of P established in Step 2. The finite-etale-category statement explicitly provides stability under base change, so it applies to B_n -> H_n, even when H_n is non-Noetherian.

For Step 4 I read the finite-data descent statement (objects and morphisms on qcqs affine-transition limits), the finite-morphism descent statement, both composition statements, and the pointed finite-etale-limit-cover statement. I checked Stacks Limits tags 01ZM, 01ZO and 07RP against their labels. Every residual stage and limit is affine, so the limit hypotheses hold. The descended etale model is of finite presentation, hence locally finite type for finiteness descent. The composite W_a -> S is finite etale. The universal-cover node's splitting is explicitly natural in finite etale S-schemes; taking the fibre of the map between these two split objects proves the claim for a cover which initially lived only over the limit. Thus no simple-connectivity theorem absent from that node is being silently assumed.

For Step 5 I read the integral-over-henselian-pair, nilpotent-base-change-idempotents and henselian-terminology statements. The first applies to a finite integral root algebra, not an etale one. The second gives idempotent bijectivity for every scheme over the nilpotent base quotient, so applying it to Spec of every finite C-algebra proves exactly the stated definition of the henselian pair (C,K). The explicit nilpotence exponent r(n-1)+1 is valid also for n=1 or r=0.

For Step 6 I read every clause of finite-etale lifting, and Stacks pione.tex Tag 09ZS, lemma-gabber. The cited node is stronger (proper schemes over all henselian pairs, Tag 0GS2), so the identity proper scheme is allowed. I use its fully faithful clause twice to lift a splitting and its inverse, not merely its essential-surjectivity clause. No locality or Noetherianity assumption is needed or inserted.

For Step 7 I read the set-valued constant-sheaf representability statement, which allows empty finite sets, and the fully faithful comparison statement. On a connected base a finite clopen partition has at most one nonempty member; this proves the uniqueness argument in a few lines. The comparison carries this precise etale assertion to pro-etale sheaves. The chosen fibre makes the splitting canonical, so later naturality is justified rather than asserted.

For Step 8 I read the actual CRT node, roots-product node, and profinite-test-objects definition. I checked the pairwise comaximal ideals by the displayed invertible differences. Quotienting successively in each variable gives the labelled finite torsor comparison, with power-map compatibility on the generators. The roots-product node applies in the algebraically closed field of the selected geometric point, with the given primitive family. Its finite coordinate identifications are the same abstract residue labels that act on H_n. The inverse limit here is of affine schemes and finite disjoint unions, not of sheaves of infinite coefficients.

Step 9 uses the connected-constant-map argument proved in Step 7, the finite torsor comparison proved in Step 8, and the identity/triple equations of the canonical descent datum. I computed its order with the stated (x,gx) convention. The abelian finite root group makes the initially reversed composition into a left action. Because the arrow is already defined over a finite root level, its action is continuous and its equality holds on the profinite-parametrized overlap itself. No uncited profinite-function theorem is needed.

Step 10 explicitly proves both directions of the Hom bijection by the sheaf axiom on the cover and double overlap; Step 11 obtains products and finite module operations from the already-proved fibre uniqueness and checks coefficient change on b tensor q. Step 12 applies that same uniqueness to pointed refinements, and checks the trivial-root case. These four steps are elementary consequences of the preceding constructions and sheaf definitions, not hidden geometric lemmas. All steps are shorter than 2000 characters.

I tested the statements and argument at r=0, n=1, the empty finite cover, the singleton sheaf, a single regular parameter, several transverse parameters, and unramified covers of degree p. The last case is an important check: total degree need not be prime to p, and the residual universal cover kills the horizontal finite etale part after ramification has been removed. The rings modulo J and modulo the new root ideal are kept distinct throughout. I found no circular citation or clause-restatement among the new node and the reused tools. The report and all search/citation records are retained for the independent maintainer review.

## Unfinished work

None in the one-level split. The new geometric input remains statement-only as required; its own future split must expose its local normalization and finite-exponent argument. The item's statement is unchanged. The returned landing is repaired below; the fresh server dry run and direct push rebase the retained split onto the current DAG.

## Previous validation (before the returned landing)

The server standalone review_split returned PASS. The server standalone check_dag returned `check_dag OK: no finding introduced by the sandbox or on its nodes`. The full `deliver.py --no-push` exited successfully with `OK (not pushed)` at e64be2976ff and `preflight passed`. This includes the actual staged delivery's search log, citation quote, DAG, split and preflight checks. The independent maintainer still reviews the mathematics after direct delivery.

## Repair of returned landing L (2026-10-22)

The refused landing reported that `lem-sfb-snc-universal-residual-charts` changed after the reviewed delivery. I retained the delivered item, new extension node, original review, citations, and actual search records. The initial required dry run exited with the specific Step 1 non-verbatim citation diagnostic; it pushed nothing. I compared the retained item with the current repository: the statement and all inherited metadata agree, while the retained proof, proof dependencies, searches, status, proof origin, and split report are the intended delivery fields.

I reread the entire current residual-chart statement and compared it with the retained full-statement quotation, normalizing its older doubled TeX escaping only for this comparison. Its mathematical changes are the explicit restriction of root levels to positive integers prime to p, ordered by divisibility, and the qualified overlap refinement through a fixed geometric point with compatible roots of units relating two labelled parameter equations. Henselianity, the identification of the residual universal cover, connectedness of finite and infinite punctured levels, and the pro-etale covering are all still stated explicitly. The item has always used prime-to-p levels, so no statement correction is needed. Step 1 now defines f and H_n, spells out this indexing and the specialization Y=V with the identity chart, and matches the actual specified residual construction. Step 12 now cites the residual-chart node directly and includes both conditions on common refinements before using its compatible tower maps. Its remaining comparison is the identity-on-the-point uniqueness argument from Step 7, so it is still elementary relative to that citation.

For the other nineteen retained step/node citation pairs I reopened the current statements and checked the verbatim quotations; all nineteen remain valid, and their conclusions are still exactly those described step by step in Review by NZ. I also reread the finite root-extension statement, ILO IX Proposition 2.1 on printed pp.133–134, Bhatt–Scholze Lemmas 5.1.2 and 5.1.4 and Corollary 5.1.5, and the current direct-images blueprint paragraph (3). No geometric input, coefficient category, or route has changed. I read the retained searches.jsonl results rather than rerunning unchanged search questions; this repair creates no additional node and makes no new Mathlib absence claim. A fresh search of the live WeilConjectures and Sheaf sources for the exact item tag and SNC tame terms returned no attachment.

I rechecked B–E: the sole new node remains self-contained and statement-only; its searches and nonduplicate distinctions are retained; every proof step uses the cited statements rather than their proofs; the refinement conditions now match the current source node; and the edge cases r=0, n=1 and the empty finite cover still work. The new explicit indexing excludes non-etale p-power transitions rather than invoking them. Both altered proof steps are below 2000 characters and hide no new lemma. The replacement Step 1 quotation is copied verbatim from the current statement, and the new Step 12 quotation is its exact overlap-refinement sentence. The dependency union is unchanged because Step 1 already used the residual-chart node. The item statement and the new geometric input are unchanged.

The required delivery tool will construct the repaired commit on the current DAG base, revalidate the staged citations and run the server preflight; no git command or repository write is performed by this worker.

## Repair validation

The repaired server dry run exited 0 with `OK (not pushed)` at `1dd4b707115` and `preflight passed`. All 21 current step/node quotations were also checked against the actual statements, including the new Step 12 citation, and the proof dependency union agrees. The item statement still equals the current repository verbatim. The final report update is followed by a final dry run and direct push of the same sandbox inputs.
