## Worker report

Files written (all under `dag/nodes/sec-six-functors-basics/`):

- `lem-sfb-space-flat-proper-fp-locality.json`: item, split into nine proof steps.
- `lem-sfb-space-local-properties-chart-test.json`: statement, unsplit; no Mathlib match for the algebraic-space chart criterion.
- `lem-sfb-space-quasicompact-fppf-local.json`: statement, unsplit; no Mathlib match for arbitrary algebraic spaces.

Attachments: none. The project-source search for the blueprint tag, algebraic spaces, and the relevant morphism properties found no declaration stating the item. Scheme results do not attach this space statement. No Lean was written or compiled.

WANTED: none.

The item had a statement and recorded searches but no proof. The proof now follows the constituent-property arguments in Stacks, not three new nodes restating the three conclusions. There are two new nodes and zero Mathlib leaves. I retained the original statement assertions, source, provenance, and searches. I repaired doubled TeX escapes and explicitly spelled out the topology, quasi-compactness and the representable meaning of closed immersion. This changes no mathematical assertion. The three properties remain separate and no Noetherian, representability, finite-presentation or extra flatness hypothesis has been added.

Nothing mathematical remains unfinished in the item's split; the two new inputs are deliberately statement-only for subsequent stage-1 work. `citations.json` quotes the actual statement, not proof text, of every node cited by a proof step. The search log and `search-results.json` retain the executed searches and complete results used here.

## Blueprint and searches

Read the chapter `sec-six-functors-basics` and the assigned unit `sk-thm-sf-ctf-stability`, together with the inherited route to the curve stack. This input supplies property descent in `quot-lemma-spaces-stack` and pullback in `quot-lemma-spaces-fibred-in-groupoids`, used by `quot-lemma-curves-stack`. The assigned node's entire `created.item` chain has a null nearest imported blueprint ancestor (`blueprint_refs.py ancestor` prints None). I retained this null and the precise inherited place, prepending this item to the new nodes' via lists; I did not invent a different ancestor or change the unit.

Searched all DAG statements and sources for Tags 03MJ, 03MM, 0410, 040Y, 03HF, 041L, 0DFQ, the lemma labels and chart/quasi-compactness keywords. Blueprint searches included `fpqc`, `source-and-target`, `universally closed`, `quasi-compact`, `closed immersion`, `03MJ`, `03H4`, `041L`, `scheme charts`, `flatness`, `local on the target`, `finite presentation`, and `0410`. No imported node states either new input. The existing proper-space base-change lemma is reused. Scheme fpqc descent and scheme base-change nodes are reused rather than copied.

For the item and each proposed new input I ran msearch LeanFinder in two phrasings, Loogle, source grep and LeanSearch, and read the returned declarations. The chart searches return scheme smooth/etale/flat facts. The quasi-compactness searches return scheme descent frameworks and scheme quasi-compactness; they do not quantify over algebraic spaces. The algebraic-space source greps have no implementation. Thus neither new input is an exact Mathlib match or a one-line specialization. I also searched the point-fibre-product claim before deciding it should be an elementary proof step rather than a new node. Its LeanSearch was rate-limited, which is logged as unavailable; its other hits concern scheme pullbacks. That abandoned candidate was not created.

## Not duplicates

lem-sfb-space-local-properties-chart-test vs lem-a1-space-lqf-atlas-refinement: the existing node constructs a pulled-back atlas and descends local quasi-finiteness for a map to a scheme; it does not assert chart independence or detection of flatness, local finite presentation, or local finite type for a morphism between arbitrary algebraic spaces. Sharing the common-refinement source Tag 03MJ does not make either statement a special case of the other.

lem-sfb-space-local-properties-chart-test vs lem-sfb-stack-finite-type-calculus: the latter treats stack finite-type operations, not simultaneous chart independence for flatness, local finite presentation and local finite type on arbitrary algebraic spaces.

lem-sfb-space-local-properties-chart-test vs lem-weil-pbc-separably-generated-separable: the apparent shared string 0410 is the decimal line number 10410 in the latter's source, not Stacks Tag 0410; its statement is about separably generated field extensions.

lem-sfb-space-quasicompact-fppf-local vs lem-trf-space-qc-separated-etale-local: the latter assumes etale scheme target covers and tests the conjunction of quasi-compactness and separatedness. It cannot descend quasi-compactness alone along flat locally presented covers, or be applied to a merely quasi-compact diagonal.

lem-sfb-space-quasicompact-fppf-local vs lem-weil-pbc-fpqc-descend-quasi-compact: the latter treats scheme morphisms and a single surjective flat quasi-compact scheme map. The new input treats nonrepresentable morphisms of algebraic spaces and arbitrary fppf families; it also supplies arbitrary space base change.

No genuine shared Stacks tags with an existing node were found for the two new nodes.

## Review by Q44

I read `spaces-descent.tex` at 041V (finite presentation), 041W (flatness) and 0422 (properness), including the proofs they invoke at 041L, 041N, 041O, 041S, 041T and 0421. For base change I read `spaces-morphisms.tex` at 03MO, 03XR and 04WP. For the new chart input I read 03MJ and the three local-characterization lemmas 03MM, 040Y, 0410: these allow an arbitrary source atlas over a target scheme, not only a single selected diagram. For the quasi-compact input I read its definition, 03HF, and 041L, with `spaces-topologies.tex` 0DFQ for fppf versus fpqc. The new statements introduce their base scheme, spaces, covers, size bounds and meanings of properties; neither contains a hidden proof or dependencies in `proof_deps`.

Step 1 uses the definition of field-valued point classes and the existing sheaf fibre-product theorem. I checked the argument directly against `spaces-properties.tex` 03H4: equality of image point classes supplies a common field extension, and the pair then gives the required fibre-product point. This is two lines from the definitions, so it is an elementary step rather than another node. It proves only surjectivity of the point comparison, not its injectivity.

Step 2 uses the new chart test, atlas existence in `def-trf-algebraic-space`, and etale-cover base change in `lem-trf-space-fibre-products-etale-covers`. I read the three cited scheme base-change statements: flat base change, clause (3) of `lem-weil-pbc-qcqs-morphism-permanence` for local finite presentation, and local-finite-type base change. None requires the other two properties. The constructed U' really is the scheme fibre product of U and V' over V; its target is the correct pullback of X, and it remains an atlas.

Step 3 uses the new quasi-compact lemma and the existing `lem-sfb-space-proper-base-change`, whose statement allows an arbitrary space base change without a representability hypothesis. The comparison of the two relative diagonals is explicitly derived from the fibre-product universal property. Quasi-separatedness uses quasi-compactness of the diagonal, not closedness.

Step 4 uses the actual finite affine-refinement conclusion of `lem-pc-fppf-affine-refinement`, the scheme-cover base-change lemma, and the definition of fpqc covering. Refinements over every affine open check exactly its second condition; this does not assume that individual original covering maps are quasi-compact.

Step 5 applies the three existing scheme fpqc descent statements to U -> T, never to the nonrepresentable X -> T. Both U_i and T_i are schemes. The chart criterion returns the corresponding space property after descent. This is the substantive atlas reduction in the source, not an invocation of a new node stating flat descent itself.

Step 6 applies the new quasi-compact lemma first to f and then to its diagonal. Its covering targets D_i may be spaces: the new lemma explicitly allows this. Flatness and local finite presentation of those covering maps were proved in Step 2 and joint surjectivity in Step 1. The diagonal identification is the one for f:X -> T. The three finite-presentation conditions are all recovered.

Step 7 uses representability of the absolute diagonal from the space definition to show that each test E -> Z of the relative diagonal is a scheme morphism. The fppf covering Z_i -> Z is a scheme base change of the original family and Step 4 makes it fpqc. `lem-pc-fpqc-descend-closed-immersion` explicitly descends scheme closed immersions along that family; its statement, not its proof, is exactly what is used. No representability of X -> T is assumed.

Step 8 uses `lem-sfb-flat-lfp-space-universally-open`, which states openness after every algebraic-space base change. Its hypotheses hold for the covering maps, regardless of flatness of f. The equality of inverse images of the closed-set image follows from Step 1 and is written out. The union of the images of the open complements proves closedness on the base. This is the closed-image argument in 041O, simplified by the openness available for fppf maps. No topological fibre product is identified with an algebraic-space fibre product.

Step 9 just assembles the four constituent properness conditions proved in earlier steps and the forward base-change implications. It uses no additional theorem. In particular, finite type comes from local finite type AND quasi-compactness.

I checked B--E against these files: all new nodes are statement-only, each notation has either an inline meaning or its definition node, sources give tags and labels, and mathematical strings have single TeX escapes. I corrected the initially offset tags for local finite type/local finite presentation and quasi-separated/universally closed by consulting the tag table. The chart criterion is a chart-comparison result; the quasi-compact lemma is a constituent property, not a clause of the item. No new proof step is over 2000 characters or hides an auxiliary comparison. The source's omitted details that this item needs (point lifting, diagonal identity, quotient closed-image calculation) are present in the steps.

Small cases checked: empty X gives the empty source atlas and vacuous local properties; an empty covering can cover only empty T, in which case X and its tests are empty. Infinite coverings and non-quasi-compact bases are handled affine open by affine open in Step 4. Non-separated flat or locally presented maps are not excluded: quasi-separatedness is supplied separately only for the finite-presentation assertion. No Noetherian or finite-type assumption is used for a covering scheme, atlas, or arbitrary base change. These checks found no statement dispute or source error.

The off-unit inputs are generic tools, declared only in `split_report.tool_uses`: scheme descent, affine cover refinement, and fibre-product calculus. They implement this unit's existing property-descent input; they do not replace its curve or alteration route.


## Repair of the landing return (2026-10-22)

The return at head `7d4ddc1f6d6` approved the mathematics but refused landing because the side completion had not been promoted to the live DAG. I compared the retained delivery inputs with the current shared DAG rather than treating the old completion as live. The current item is `unsplit`, has no proof or split report, and has no released stage-1 repair note. Its non-split-owned fields agree with the retained item; neither of the two new input ids exists in the current DAG. The official delivery dry run rebuilt the delivery against the current server DAG and passed at `826dc7abbb1` before these repair annotations; the final dry run below must validate the revised files afresh.

I re-read every existing statement cited by the nine steps and checked it against the complete statement saved in `citations.json`. Every saved quote still agrees verbatim, so there is no changed cited statement requiring a new dependency or a different hypothesis. In particular the three scheme base-change inputs still give the three separate local properties in Step 2; the affine-refinement and fpqc-definition statements still justify Step 4 for arbitrary fppf families; the three scheme descent inputs still apply to the scheme atlas in Step 5; the closed-immersion descent statement still applies only to the scheme tests in Step 7; and the algebraic-space proper-base-change and universal-openness statements still allow arbitrary space pullbacks in Steps 3 and 8. The point-class definition and fibre-product statement still support Steps 1, 3, 6 and 7. The two new input statements remain exactly those reviewed above.

I also reopened `spaces-descent.tex` at the labels for flatness, finite presentation, properness, quasi-compactness, quasi-separatedness, separatedness and universal closedness, and `spaces-morphisms.tex` at the chart-comparison, local-property and base-change labels. Their hypotheses still support the retained proof. I tightened Step 3 by writing the actual map $D' \to D$ and the identity $X\times_DD'\cong X\times_YY'$, including its compatible-point calculation. Thus quasi-separatedness uses the base change of the relative diagonal along its target, with no implicit identification of point sets. This is a clarification of the same elementary fibre-product argument and introduces no new lemma or search question.

The retained search log and full result file were read again; no search has been invented or rerun. The statements of the item and both new inputs are unchanged by this repair. Empty-source, empty-cover and infinite-cover checks remain as in the signed review. All proof steps remain below 2000 characters. The delivery carries the renewed current-DAG audit and the explicit diagonal square, rather than only an unchanged re-push. The authorized delivery tool performs the rebase and server checks; only the sandbox was written.


## Renewed rebase audit by Q44

The required first dry run of this retry completed successfully at `2d9413491c4`. I compared the retained files with the current shared DAG: the live item is still unsplit, both supporting-node ids are absent, and no released repair note changes the task. The item differs by its approved proof, searches and the explicit definitions already described above; its original property assertions and source are preserved. The official delivery tool rebases these sandbox inputs onto the current server DAG.

I re-read all existing proof-dependency statements and checked all 29 saved citation entries against them: every quote is still verbatim and every step's cited nodes are covered. Thus there is no changed cited statement to repair. Scheme descent is still applied to scheme atlases or scheme tests, while the quasi-compactness input covers arbitrary algebraic-space targets. I reopened the Stacks proofs of flat, finite-presentation and proper descent and their chart, quasi-compactness and diagonal ingredients. The chart and quasi-compactness input statements still have the hypotheses these steps require. The retained search results continue to concern schemes or rings, so they do not attach or discharge these space statements; no search question changed and the executed-search log is retained.

I further repaired the wording of Step 3: its diagonal calculation now gives a natural bijection on sections over every test scheme W and tracks the projection to D-prime. This establishes the claimed sheaf isomorphism and its diagonal map directly from the cited fibre-product universal property; it does not infer that isomorphism from underlying point sets. This is a substantive clarification of the retained approved argument, with no new lemma or hypothesis. All nine steps remain shorter than 2000 characters. The empty and infinite covering cases, source/target distinctions and separate-property hypotheses remain valid as checked in the signed review. The final dry run is rerun after these changes before the push.


## Current-DAG repair audit, 2026-10-23

The required initial dry run exited before building the delivery because the current DAG has the newly landed `lem-a1-space-lqf-atlas-refinement`, sharing Tag 03MJ with the chart-test input. I opened its complete statement and proof. It proves a natural atlas pullback comparison and common-refinement criterion for local quasi-finiteness over a scheme B. It does not state any of the three local properties used here, nor a criterion for a general algebraic-space target. The retained chart-test statement therefore cannot be replaced by that node. I added the exact pair and distinction under Not duplicates. This repairs a new failure of the current-DAG preflight rather than repeating the old delivery unchanged.

I compared the current unsplit item with the sandbox item, and re-read all eighteen proof-dependency statements (the two sandbox inputs and sixteen existing inputs). All 29 saved citation quotes are still verbatim and cover every step-use pair. In particular the scheme descent lemmas still require exactly the fpqc family established in Step 4, the chart criterion still permits the scheme atlas in Step 5, and the quasi-compactness lemma permits the algebraic-space targets of the diagonals in Step 6. No changed cited statement requires a replacement. The two new node ids remain absent from the shared DAG, and no released repair note exists. The live Lean search for the item tag and algebraic-space terminology has no exact project declaration; no attachment is justified.

I reopened the Stacks source statements and proofs at the flatness, finite-presentation, properness, separatedness, universally-closed and quasi-compactness descent labels, together with the chart-locality and local-property labels. The retained constituent-property route still matches their hypotheses. I additionally made Step 7's representability test explicit: the scheme E testing the relative diagonal is the test of the absolute diagonal at the same map from Z to X times_S X. This follows directly on sections, retaining the original base S and avoiding an unnecessary change of base convention. It provides the precise scheme to which closed-immersion descent applies.

The earlier search log and recorded search results are retained: all hits concern schemes/rings or abstract descent frameworks and none states the algebraic-space inputs. No mathematical search question or statement changed, so I reused rather than repeated those searches. The B--E check still finds statement-only new inputs, no clause-restatement, complete sources, no missing node uses, no proof step above 2000 characters, and no additional hypothesis. Empty sources/targets and infinite covers remain covered by the signed review. The final dry run and push use the authorized delivery tool to rebuild on the current server DAG; no repository or launcher file was written.
