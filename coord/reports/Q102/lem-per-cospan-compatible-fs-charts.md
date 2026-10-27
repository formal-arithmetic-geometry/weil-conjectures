## Worker report

Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-cospan-compatible-fs-charts.json` (item, split, ten proof steps), `citations.json`, and this report. `searches.jsonl` contains the actual search-command log; `write_split.py` is sandbox scratch only. The imported statement and statement dependencies are unchanged.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves. The existing DAG already supplies the non-elementary monoid, chart-spreading and scheme inputs. In particular this delivery does not create a lemma restating compatible charts for a single morphism or for the whole cospan.

## Attachments

None. Searches in the live `lean/WeilConjectures/` by the exact blueprint tag and by `LogStructure`, `LogScheme` and logarithmic chart terminology found no declaration of this logarithmic statement. Occurrences of logarithmic derivatives concern power series and do not supply log schemes. No compiler, Lake or build command was run.

## Literature wanted

WANTED: K. Kato, *Logarithmic structures of Fontaine--Illusie* (1988), section 1, chart and associated-log constructions, for lem-per-cospan-compatible-fs-charts. This is already requested in the item's source. The proof here does not pretend that the unavailable chart lemma was read: arbitrary-morphism compatibility is explicitly constructed from existing algebraic and spreading statements. No download or literature-file change was made.

## What needed repair

The original node was statement-only. ILO X Theorem 3.5 Step 6 discusses two particular charted log morphisms and their pushout; it does not prove the general arbitrary-morphism compatibility asserted by this node. Simply invoking that paragraph would leave the real section maps and unit factors unchecked. Steps 2--5 instead construct a compatible source chart for the fixed target chart: split the sharp characteristic, record all unit coordinates of its finitely many target generators, and adjoin their generated subgroup. This avoids extracting any roots of units, including in positive characteristic. A sharp source chart alone would generally omit the needed unit factors.

No statement dispute was found. There is no hypothesis change or route change. The underlying ordinary fibre product is assumed locally Noetherian exactly where step 7 needs it; local Noetherianity of X,Y,Z alone would not justify that inference. ILO's printed page 164 uses Zariski charts in its special geometric setting; our statement uses etale charts, as in VI 1.1, without imposing that special setting.

Nothing mathematical remains unfinished at this split level; cited unsplit nodes retain their own work. Delivery and server validation are recorded below when completed.

## Blueprint and duplicate searches

Read the current `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/` ancestor statement and proof, together with the unit and chapter records. `blueprint_refs.py ancestor` gives `lem-per-artin-gabber-affine-curve`. The existing `blueprint.from.place` identifies the regular-pair-purity/logarithmic-comparison ancestry below its Step 3 and is retained. Whole-blueprint searches for `chart`, `compatible chart`, and `face sharpening`, and whole-DAG statement/title searches for compatible logarithmic charts, prescribed chart morphisms, fs face sharpening, finite stalk data, etale products and coverings found the existing tools cited in the proof. No blueprint node states this arbitrary cospan chart lemma. No new node was created.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Reused `lem-trf-chart-face-localization-logification`, `lem-trf-fs-face-sharpening`, `lem-trf-fine-log-stalk-chart-spreading`, `lem-trf-finite-monoid-stalk-data-spreading`, and `lem-trf-associated-log-universal-stalks` instead of duplicating their assertions.

## Mathlib searches

The five new queries in searches.jsonl were run through the prescribed msearch.py command: grep `LogStructure|LogScheme|FineSaturated` in AlgebraicGeometry (zero hits); Loogle `"LogStructure"` (zero hits); LeanSearch for etale local compatible cospan charts; and LeanFinder for compatible fs charts and, in a second phrasing, source charts enlarged by finitely many units. All services answered. I read the returned signatures: ordinary etale sites, ordinary scheme spread-out maps and fibre products, manifold local charts and the valuative criterion do not give monoid charts for logarithmic schemes. The exact queries and returned metadata were appended to the item's existing search history, without rewriting the Q30 searches as newly performed ones. Thus this item is not a Mathlib leaf.

## Review by Q102

I read ILO VI 1.1 (printed p.69) for the etale/fs conventions, VI 3.7(a) (p.75) for splitting the free characteristic group and spreading its chart, VIII 3.1.1--3.1.5 (pp.98--99) for localization/sharpening, and X Theorem 3.5 Step 6 (p.164) for the ordinary product and pushout-chart use. VI 3.7(a) has log-regular and group-action context; I do not import those hypotheses into this item or use its equivariance assertion. Instead the cited DAG algebraic face/localization lemmas state the general fs consequences needed here. I also opened the cited scheme-node statements and the Stacks source for locally Noetherian schemes, etale openness/flatness, and fpqc coverings. No SGA route is used.

Step 1: the fs definition gives chart coverings, not a point lift, so I separately cite `lem-weil-pbc-etale-cover-geometric-point-lift`. `lem-weil-pbc-affine-opens-basis` justifies the affine shrink. Etale base change and `pqf-lem-locnoeth-lft` supply the Noetherian hypothesis on both new source bases; etale local finite presentation implies local finite type by forgetting the finite relation list. Restricted etale log charts remain fs by the definition. The common geometric field is kept throughout.

Step 2: I opened both `lem-trf-chart-face-localization-logification` and `lem-trf-fs-face-sharpening`. The former explicitly gives the stalk pushout and characteristic identification; the latter explicitly says the sharp quotient's group completion is finite free. Neither requires log regularity. I use their statements, not their proofs.

Step 3: the same two statements suffice. The section is constructed by choosing basis lifts, then checking that its values on C lie in T because their difference from any monoid lift is a unit. Both inverse formulas for the direct sum are written. This is an elementary consequence of the cited free quotient and unit subgroup, not an uncited group-splitting theorem.

Step 4: this is an explicit construction from the chart definition and the preceding splitting, with no new black box. The unit subgroup V includes inverses, so it is a finitely generated group even if the target chart has relations or torsion units. Saturation of C proves saturation of Q inside its own group completion; no saturation in a larger ambient group is being asserted. The two displayed maps check the associated-log quotient isomorphism, and the equality qh=a retains the actual unit coordinates. This is why I did not create a separate elementary unit-envelope node.

Step 5: `lem-trf-fine-log-stalk-chart-spreading` explicitly accepts the prescribed integral chart germ and returns an affine pointed neighbourhood. `lem-trf-finite-monoid-stalk-data-spreading` explicitly states injectivity/eventual equality for the two homomorphisms out of the finitely generated P; merely having a chart would not say that. `lem-trf-associated-log-universal-stalks` says chart data determine the morphism uniquely and that units are fixed, exactly the assertion used for the actual log map after pullback. Its assumptions hold for the restricted locally Noetherian source. The point/germ identifications are those in the spreading statements.

Step 6: this repeats the already written construction with the same target chart, rather than choosing two unrelated charts of Z. `def-per-strict-log-morphism` gives the associated-log pullback property; the associated-log universal property gives the identical P chart on a strict leg. No cancellation of a unit factor is assumed. Etale composition and affine shrinking are separately cited. Both strict legs can use P simultaneously.

Step 7: `lem-weil-pbc-fibre-product-affine-spectra` states affineness for two affine schemes over an affine base. Etale base change and composition give the three-map factorization to W. The fibre-product point exists because both lifts have the same Spec(Omega) map to Z_0. Only after this do I use W's local Noetherianity and Noetherian ascent. `pqf-def-locnoeth` gives a cover by affine opens with Noetherian coordinate rings; I choose H from that cover, avoiding the unsupported assertion that every affine ring is Noetherian merely because an unspecified local condition holds. Opens of such local Noetherian schemes are locally Noetherian as explicitly stated in that definition node.

Step 8: the formula on Q plus R is multiplicative and equal on each stated relation because of the actual chart compatibility from steps 5--6. Factoring a homomorphism through a congruence quotient is elementary. The ordinary pushout is not claimed to be saturated or integral.

Step 9: I opened `lem-weil-pbc-etale-morphism-open-map` and `lem-weil-pbc-affine-scheme-qcqs`; they state openness and quasi-compactness, respectively. These give finite extraction from the actual affine refinements over D. I take refinements inside its inverse image, so their images have union exactly D, as the fpqc definition requires, not just a union containing D. Flatness is part of `def-weil-etale-morphism`. The result is checked against the precise finite-affine-opens clause of `def-weil-pbc-fpqc-covering`.

Step 10: `lem-weil-pbc-scheme-coproduct-family` covers arbitrary set-indexed families and gives open disjoint components. The map on local rings is the component map, so flatness follows pointwise from `def-weil-flat-morphism`. The finite affine witnesses of step 9 remain opens in the coproduct and verify the singleton fpqc definition; no quasi-compactness of the whole infinite coproduct is assumed.

Edge cases: trivial log structures permit C=0; empty generator lists give V={1}; torsion units stay in a group factor and do not demand roots; a nontrivial unit twist is explicitly included by h(p)=(v(p),u(p)). Noninjective and non-Kummer chart maps are allowed throughout. Both strict legs give identity chart maps. Empty W uses the empty family and zero finite opens. No proof step exceeds 2000 characters; the largest is the elementary unit-envelope computation. Every non-elementary input is an existing cited statement, and citations.json supplies its verbatim statement for every occurrence. I declare the off-unit generic tools in split_report.tool_uses for maintainer assessment; they implement the existing logarithmic-comparison ancestry rather than replace the perverse unit's route.

I checked delivery-errors B--E: no new statement-only node or unintroduced new notion is added (B); actual section equalities, Noetherian ascent, etale stability, openness, coproduct existence and the log universal property are cited explicitly (C); the proof performs the chart construction rather than passing the conclusion to a renamed node (D); all point, finiteness, locality and strictness hypotheses above are in force (E). The corrections during self-review were to keep unit factors, enforce equality after spreading, use W's stated Noetherian hypothesis, and choose finite refinements whose images lie in the affine target open.
