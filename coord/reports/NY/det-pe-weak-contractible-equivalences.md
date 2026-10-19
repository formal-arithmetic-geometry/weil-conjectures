# Stage-1 worker report: det-pe-weak-contractible-equivalences

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-weak-contractible-equivalences.json`: statement, split; no exact Mathlib match for the whole assertion. Five proof steps reuse existing DAG nodes.
- `citations.json`: six verbatim statement extracts covering every node cited by the five proof steps.
- No new nodes; no new Mathlib leaves.

## Attachments

None. Searches for the blueprint tag and for weak contractibility in the project source found no declaration stating all clauses. The upstream master source is reference material only; no upstream sorry declaration was treated as a finished proof.

## WANTED

None. The current blueprint proof and the Stacks sources needed for the expansion are available locally.

## What was wrong in the node, blueprint or brief

The imported proof left Yoneda and pullback stability of sheaf epimorphisms uncited and had null elementary flags. The complete natural Yoneda evaluation theorem already exists as `lem-galois-yoneda-hom-bijection`. Pullback stability here is a few-line consequence of the existing set-sheaf local-surjectivity leaf, so I wrote out the sectionwise pullback and local lifting in the item's steps. No new supporting node is needed. The statement and every imported blueprint/import flag were preserved. I added statement dependencies for the sheaf category and w-contractible ring notions.

The item has no chapter/unit metadata. The current chapter record `dag/chapters/sec-proetale-coefficients.json` is available and was read; there is still no corresponding weak-contractibility unit record in dag/units. I read both current blueprint `_section.md` files and followed their explicit route through a pullback epimorphism and identity lifts. No maintainer metadata or unit record was changed.

Whole-blueprint search found `sk-def-pe-weak-contractible`, whose definition includes the same equivalences, so it is recorded in `blueprint.same_as`. It is not cited as a proof of the equivalences. The item additionally records the existing affine w-contractible conclusion.

Mathlib searches were made with msearch.py and are recorded verbatim with verdicts. The first grep calls supplied `Mathlib/CategoryTheory` as the subdirectory, but the script already adds `Mathlib/`, so they returned zero hits against the wrong directory and are not evidence of absence. I reran grep using the correct `CategoryTheory` subdirectory: it found yonedaEquiv (Yoneda.lean:724) and the projectivity/coyoneda API. I read the naturality formulas at Yoneda.lean:747–760 and Preadditive/Projective/Basic.lean:45–56; these provide ingredients, not all clauses including the w-contractible affine assertion. Loogle identifier errors are retained as returned and are not interpreted as absence of the relevant theorem.

## What could not be finished

Nothing remains in the requested one-level split. Dependencies already in the DAG remain separate items. No Lean was written and no compiler or Lake command was run.

## Not duplicates

No new nodes are delivered. The generic Yoneda evaluation and set-sheaf epimorphism criterion are reused. The statement overlap with the existing weak-contractibility definition is recorded in same_as without creating a circular proof dependency.

## Review by NY

I read the current item statement/proof and both containing `_section.md` files under `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`. I also read Stacks `categories.tex`, Tag 001P (`lemma-yoneda`), including its arbitrary-presheaf natural bijection and explicit inverse, and `sites.tex`, Tags 00WM/00WN (`definition-sheaves-injective-surjective` and `lemma-mono-epi-sheaves`). This follows the permitted blueprint/Stacks route and uses no SGA source.

For step 1 I opened all three cited statements. `det-pe-topos-functoriality-site` explicitly says every representable is a sheaf, `def-weil-pbc-sites-and-cohomology` says sheaves form the full subcategory of presheaves with natural transformations as morphisms, and `lem-galois-yoneda-hom-bijection` gives the full evaluation bijection, including naturality in the target presheaf. Thus the same two sheaf morphisms are compared under Yoneda and equality of their evaluations proves equality of morphisms; full faithfulness of Yoneda alone would not have sufficed.

Step 2 cites the sheaf definition for its equalizer condition and separatedness. I checked the pair presheaf has well-defined restriction maps by naturality, that each matching coordinate glues uniquely, and that equality in G descends by separatedness. Its projection maps and universal pairing show it is actually the claimed pullback, rather than relying on an unstated existence theorem.

Step 3 cites `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`. I read its full statement: it gives both directions of epi iff locally surjective for sheaves of sets on any site. Applied to alpha and y(t), its cover produces pairs lifting t locally; applied again to the projection, it proves that projection epimorphic. No abelian-sheaf, pointwise-surjective, or small-index limit theorem is substituted. Step 4 has no outside theorem: composing the section with the other projection gives alpha q r = y p r = y, while lifting the identity gives the converse.

For step 5 I opened `det-pe-wcb-projective`: clause 1 explicitly says every sheaf-of-sets epimorphism onto h_U has a section for an affine site object Spec D with D w-contractible. These are exactly the item's last hypotheses; affineness and w-contractibility are used only here. I also read `sk-def-pe-wlocal` for the w-contractible definition used in stmt_deps. I generated every citation quote directly from the corresponding current node statement and checked it is a literal substring.

I checked delivery-errors B–E against the final files. There are no new unsplit statements, duplicate nodes, missing Mathlib citations, statement changes, SGA references or hidden proof sketches. Every non-elementary ingredient is a cited existing statement; the pullback construction and its local lifts are elementary deductions explicitly written in steps 2–3. The proof does not cite the proof of the existing projectivity node. The dependency union equals proof_deps and the overlapping definition is not a dependency. The zero ring/empty affine case causes no exception: empty matching families glue uniquely by the sheaf condition, so evaluations at the empty object are singletons. For a general disconnected W no lift to a single covering member is asserted; local lifts only construct the pullback epimorphism and hypothesis 1 supplies a section of that sheaf. No quasi-compactness or affine hypothesis is used in the three equivalences.

## Earlier second reading (a previous round; superseded)

I independently read delivery-errors B–E, GOAL.md and coord/dag-sync.md; the current main-20261015 chapter and weak-contractibility unit; the item's statement and proof files; all five distinct cited node statements; and the w-contractible definition. The item agrees clause by clause with `sk-def-pe-weak-contractible/det-pe-weak-contractible-equivalences.md`. No statement dispute or route change was needed. I checked the Stacks tags against `tags/tags` and opened the actual labelled text, rather than relying on the first reader's report.

- Step 1: PASS against `det-pe-topos-functoriality-site` clause 2, the full-subcategory clause of `def-weil-pbc-sites-and-cohomology`, and the complete statement of `lem-galois-yoneda-hom-bijection`; Stacks `categories.tex` Tag 001P, `lemma-yoneda`, explicitly covers arbitrary target presheaves. Mathlib `Yoneda.lean:724–760` supplies the bijection and target naturality. The displayed commuting equality and injectivity of the bijection justify both directions with no extra hypotheses.
- Step 2: PASS against the sheaf equalizer definition in `def-weil-pbc-sites-and-cohomology` and Stacks `sites.tex`, `definition-sheaf-sets` (Tag 00VM). Coordinatewise restrictions preserve the equality; each coordinate glues, separatedness of G proves the equality after gluing, and component pairing proves the universal property. This is an elementary construction, with no hidden assumption that epimorphisms are pointwise surjective.
- Step 3: PASS against both directions of `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`; Stacks Tags 00WM/00WN, labels `definition-sheaves-injective-surjective`/`lemma-mono-epi-sheaves`, give exactly local lifts for each section on each site object. The pairs displayed in this step prove local surjectivity of the projection in a few lines. The cited Mathlib declaration `Sheaf.isLocallySurjective_iff_epi` was also read at `Sites/LocallySurjective.lean:378–388`.
- Step 4: PASS against the split-epimorphism condition in clause 1 and the lifting condition in clause 2 of the item. The equation uses the pullback equality and p r = id, and lifting the identity proves the reverse implication. This is elementary composition, not an additional topos theorem.
- Step 5: PASS against clause 1 of `det-pe-wcb-projective` and its current blueprint statement. Both require an affine site object Spec D and w-contractibility of D, exactly as in the item. Only this final assertion uses these hypotheses; no field or connectedness hypothesis is introduced.
- New nodes: none; B1–B7 and the duplicate/restatement/Mathlib-leaf tests introduce no additional obligations. No new Mathlib leaves. I independently searched the DAG for Tags 001P/00WM/00WN and the source checkout by the item id and weak-contractibility vocabulary. The existing generic Yoneda and set-sheaf local-surjectivity nodes are reused, and no matching finished declaration of the complete item was found.

Small cases: for the empty affine/zero ring, the empty covering forces F(empty) and G(empty) to be singleton sets (also stated in Stacks `remark-sheaf-condition-empty-covering`); the evaluation condition and unique lifting argument remain valid. For a separably closed field the w-contractible hypothesis has its intended meaning; an arbitrary field is not asserted to satisfy it. A disconnected object is never claimed to lift into one covering member: local pairs produce an epimorphism of sheaves, and condition 1 supplies its global section. There is no n-parameter. Steps 1–4 apply to every site object W and do not assume affineness, quasi-compactness, connectedness or a zero object in the category of sheaves of sets.

Changes made: corrected the two wrong-directory grep verdicts to say that they supply no evidence of absence; corrected the Loogle unknown-identifier verdict to record an invalid query; clarified the zero-hit conjunction query and the related-but-incomplete LeanSearch results; added my independently run LeanFinder query about split epimorphisms and my grep using Mathlib's projectivity/splitEpi vocabulary, with their actual logged results. The hits include coyoneda projectivity and zero-object lifting-property results, not the whole item. The latter hypotheses do not hold for general sheaves of sets and were not used. I preserved the mathematical statement, proof steps, dependencies, source, first reader's sections and all six valid verbatim citation quotes. All citations were rechecked as literal substrings of the corresponding current statements.

Delivery-tool outcome: after the completed second reading, I ran the required `deliver.py NY det-pe-weak-contractible-equivalences --no-push` twice. Both processes terminated with exit code 143 and no preflight output. During the waits, read-only process/lock inspection showed serialization on `worktrees/locks/deliver-NY.lock` and `weil-newtargets.fetch.lock`; no mathematical or citation failure was returned. I did not change the launcher, remove locks, kill other deliveries, run git myself, or push without an OK dry run. The repaired sandbox is ready for the delivery tool to be retried when the interruption is resolved.


## Resumed verification by NY

I reopened the current blueprint statement, its proof and both containing section files, and reread all five cited node statements and the w-contractible-ring definition. The imported statement is still unsplit on the shared baseline and is unchanged in the sandbox. The local source search for the item tag and weak-contractibility vocabulary found ring-level retraction results, but no project declaration stating this whole sheaf-theoretic item. The existing proof preserves the unit's route: Yoneda for 2 iff 3, the explicit pullback and its locally surjective projection for 1 implies 2, and the identity lift for the converse. The affine conclusion uses exactly clause 1 of det-pe-wcb-projective; its current dependency list does not cite this item.

I checked Stacks categories.tex Tag 001P (lemma-yoneda), sites.tex Tag 00VM (definition-sheaf-sets), and Tags 00WM/00WN (definition-sheaves-injective-surjective/lemma-mono-epi-sheaves) against the actual labelled text. These support the precise bijection, matching-family gluing and local lifting used in steps 1–3. In steps 2–3, no pointwise surjectivity is assumed: local lifts give pairs in the constructed sheaf, then the same criterion proves the projection epimorphic. Step 4 is the displayed composite equality. The empty cover gives singleton evaluations, including for the zero-ring affine, and disconnected objects require no choice of a single covering member. No new hypotheses, statement correction, new nodes or route substitution are needed.

All six quotes remain verbatim substrings of the current cited statements, and the union of the proof citations is exactly proof_deps. Every inherited Mathlib query is backed by the sandbox log. I corrected the imprecise Mathlib projectivity path in the report: it is CategoryTheory/Preadditive/Projective/Basic.lean, although the first part of that file concerns arbitrary categories. A fresh msearch.py grep confirmed the declarations at lines 48 and 141; I read their statements at lines 40–60 and 135–151, alongside Yoneda.lean:724–760 and Sites/LocallySurjective.lean:378–388. This changes only the search/source record. The first resumed required dry run again exited 143 with no preflight output; the final retry result is recorded in resumed-dry-run.log.


Resumed delivery outcome: the first normal invocation exited 143 without preflight output; the second normal invocation exited 137, also without preflight output. Read-only inspection during the retry showed it waiting for a shared worktree slot and numerous other deliveries waiting on the shared fetch lock; the lock holder was itself running preflight. No failure about this item's mathematics, citations, searches or schema was produced. I did not change launcher code or lock configuration, remove locks, kill competing processes, bypass fetch/preflight, or push. The historical dry-run.log records an older acceptance, not acceptance of the current source-record repairs. The current sandbox therefore remains BLOCKED on the required tool run; rerun the normal --no-push command before reporting READY.


## Retry review by NY

I reread the current blueprint chapter, weak-contractibility unit, item statement and proof, and the six dependency statements (five distinct proof citations plus the ring definition). The shared item still has status imported, while det-pe-wcb-projective is now split and its proof dependencies do not include this item. Its first clause remains precisely the affine input for step 5. I verified all six citation quotes as literal substrings, checked their step assignments, and checked proof_deps against the union of uses. No mathematical repair was needed.

I checked the actual Stacks text at categories.tex:541 (Tag 001P, lemma-yoneda), sites.tex:918 (Tag 00VM, definition-sheaf-sets), sites.tex:2240 (Tag 00WM, definition-sheaves-injective-surjective), and sites.tex:2256 (Tag 00WN, lemma-mono-epi-sheaves). The last source omits its proof, but this delivery uses the existing Mathlib leaf, whose recorded declaration was read at CategoryTheory/Sites/LocallySurjective.lean:378. I also reread Yoneda.lean:724–760 and Preadditive/Projective/Basic.lean:48 and :141. In particular, step 1 uses target naturality, step 2 explicitly proves sheaf gluing and the pullback universal property, step 3 applies both directions of local surjectivity with the correct site and sheaves of sets, and step 4 is the displayed composition with a section. Empty covers and disconnected objects introduce no missing hypothesis.

A fresh project-source search by the exact blueprint id and weak-contractibility vocabulary found no declaration of the complete item; the ring-level retraction results do not state the sheaf equivalences. A whole-blueprint search again found only the item and the overlapping weak-contractibility definition already listed in same_as. All twelve preserved Mathlib query records are backed by searches.jsonl; none was invented or rerun outside the required search command. I corrected the stale report sentence that had claimed the chapter JSON record was unavailable. No new nodes, Mathlib leaves, statement changes, or route changes are introduced. The required normal dry run is being retried without a push; its result will be left in retry-dry-run.log.

## Second reading by NY

- Item statement: checked clause by clause against the blueprint file `det-pe-weak-contractible-equivalences.md`; representability, all three equivalences, and the affine w-contractible conclusion agree, with no added or dropped hypotheses.
- Step 1: checked against `det-pe-topos-functoriality-site` (subcanonicality), `def-weil-pbc-sites-and-cohomology` (full sheaf subcategory), and `lem-galois-yoneda-hom-bijection` (evaluation bijection and naturality); the displayed Yoneda transport proves 2 iff 3.
- Step 2: checked against the sheaf equalizer statement in `def-weil-pbc-sites-and-cohomology`; coordinatewise restrictions, gluing, separatedness, and the pairing universal property give the stated pullback sheaf. The construction is elementary and explicit.
- Step 3: checked against both directions of `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`; local lifts give the projection's local surjectivity and hence epimorphy, with no pointwise-surjectivity assumption.
- Step 4: checked against the definitions of sections, lifts, and the pullback equation; composing the section proves 1 implies 2, and lifting the identity proves 2 implies 1. This is elementary.
- Step 5: checked against clause 1 of `det-pe-wcb-projective`; its affine and w-contractible hypotheses exactly match the final assertion.
- New nodes: none. B1–B7 therefore introduce no new node obligations; DAG searches found no duplicate supporting node to create and Mathlib searches found no declaration of the complete item. The overlap with `sk-def-pe-weak-contractible` is recorded only in `blueprint.same_as`.
- Edge cases: empty-cover/zero-ring evaluations remain singleton and the arguments still work; disconnected objects require only local lifts, not one global covering member; no field, connectedness, or numerical-index hypothesis is present.
- Sources and citations: reread Stacks `categories.tex` Tag 001P and `sites.tex` Tags 00VM, 00WM, and 00WN; all six entries in `citations.json` are literal substrings of the cited current node statements. No SGA source is used.
- Changes: no mathematical or node changes were needed; this section records the completed second reading and preserves the prior search corrections and delivery history.
