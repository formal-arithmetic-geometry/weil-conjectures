# Stage-1 delivery: lem-trf-strict-log-blowup-cartesian

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-strict-log-blowup-cartesian.json`: statement, split into seven proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-zariski-fs-monoid-chart.json`: new statement-only node, unsplit; no Mathlib match. It supplies Zariski local fs charts and does not assert base change, preservation of characteristic sheaves, ideal coherence, or a blowup comparison.
- `citations.json`: a verbatim statement quotation for every node cited in every proof step.

There is one new node and zero Mathlib leaves. The item's statement, statement dependencies, source, ancestry and maintainer fields are retained.

## Attachments

None. The exact blueprint tag and logarithmic-structure/blowup terms were searched in `lean/WeilConjectures/`; there is no declaration of this item or of the new chart-existence statement. The existing general chart and blowup DAG nodes are reused, irrespective of whether their Lean proofs are finished.

## WANTED

None for this split. The proof follows the available ILO text and cites existing nodes for the associated-log facts; it does not claim to have read the unavailable Kato source mentioned in those nodes' own provenance.

## Problems found and changes made

The item was unsplit and the sandbox had no earlier item, report, citations or search log. No statement correction was needed. The source's phrases “F is also a chart” (VIII 3.3.8) and “obvious universal property” (3.3.9) needed actual arguments, including the log-section maps. The split now computes the characteristic map using the face of chart elements that map to local units, proves the ideal equality by explicit generators, and applies two universal properties to prove the Cartesian assertion. Strictness is checked separately on the common saturated fraction charts, rather than inferred merely from being a Cartesian square.

The latest blueprint `lem-trf-local-term-locality` and its unit now follow contracting correspondences; the ILO alteration branch is historical. This item's inherited provenance explicitly describes that historical branch. I retained it and did not claim that logarithmic modifications occur in the current blueprint proof, or change the unit/chapter route. Its role remains the strict base-change subargument of the existing `lem-trf-log-fan-chart-blowup` split.

The same-unit associated-log universal-property node only quantifies over maps over the identity scheme. Step 1 and the strict chart check need the arbitrary-scheme-map mapping bijection. The existing `lem-per-integral-chart-logification-thickening` states exactly that more general bijection; only this clause is used, with no thickening hypothesis or thickening conclusion. It is declared as a generic tool in `split_report.tool_uses`.

## Searches and reuse

I read ILO Expose VI 1.1 and 1.6, and VIII 3.3.2--3.3.13 in the available PDF (printed pp.69--70 and 106--109). The primary places for the item are VIII 3.3.8--3.3.11, and for the new node VIII 3.3.4(ii), last sentence. The fs version uses the sharp fs characteristic monoid as chart monoid; the new node deliberately leaves this chart-existence argument to its own later split. No SGA source is used.

Whole-DAG statement searches for Zariski logarithmic structures, chart existence, associated log structures, strict characteristic comparisons, and coherent log blowups identified the existing nodes listed below. `blueprint_refs.py search` returned no matching blueprint nodes for “log structure”, “Zariski log”, “monoid chart” or “log blowup”; the incidental matches for “logarithmic” concerned zeta functions and tensor traces, not logarithmic geometry. `blueprint_refs.py ancestor` gave `lem-trf-local-term-locality`, and the new node's via list prepends this item to the item's existing via list. I searched the whole DAG for the new id and relevant notions and read the nearby statements before writing it.

All new Mathlib search records are the actual `msearch.py` queries in `searches.jsonl`. The new chart-existence node has two semantic phrasings, LeanSearch, Loogle and source grep; the item has its own two semantic phrasings, LeanSearch, Loogle and source grep in addition to its retained earlier searches. I read all returned types. They concern ordinary schemes, localizations, Zariski sites, ordinary ringed-space stalks or finite-type module generators. The dedicated `LogStructure`/`LogScheme` and logarithmic-structure source searches found nothing. The broad expression `Zariski.*log` also matches ordinary “Zariski topology”; those hits do not give log charts. There is no one-line specialization of the returned declarations to either node.

## Not duplicates

lem-trf-zariski-fs-monoid-chart vs lem-trf-monoid-chart-characteristic-fan: the latter starts with a global fs monoid chart and computes its fan/characteristic sheaves; the new node obtains such a chart from the hypothesis that an fs structure is associated to a Zariski structure.

lem-trf-zariski-fs-monoid-chart vs lem-trf-fan-chart-local-monoid-lift: the latter assumes a prescribed global fine fan chart and lifts that specific chart on Zariski neighborhoods; the new node assumes no fan chart and is not a specialization of that hypothesis.

lem-trf-zariski-fs-monoid-chart vs lem-trf-fine-log-stalk-chart-spreading: the latter assumes a specified chart on a geometric stalk and provides an etale neighborhood; it neither gives Zariski neighborhoods nor starts from the Zariski-origin hypothesis alone.

lem-trf-zariski-fs-monoid-chart vs lem-trf-log-fan-chart-blowup: the latter provides etale fan-chart neighborhoods and pulls back fan blowup towers; the new node provides Zariski monoid charts for a given Zariski log structure, without fan blowups. That broader tower node already depends on this item and is not used here.

lem-trf-zariski-fs-monoid-chart vs lem-trf-fan-center-local-blowup-charts: the latter assumes a fan chart and describes blowups of a pulled-back fan center; it does not provide monoid charts from just Zariski origin.

lem-trf-zariski-fs-monoid-chart vs lem-trf-associated-log-universal-stalks: the latter constructs the associated log structure of a given constant-monoid prelog structure and proves its mapping/stalk properties; it does not give a constant-monoid presentation for a log structure initially defined only as a monoid sheaf.

lem-trf-zariski-fs-monoid-chart vs lem-trf-strict-log-blowup-cartesian: chart existence on a single Zariski fs log scheme is a supporting input, with no morphism g, characteristic pullback conclusion, coherent center or blowup. The item's seven steps carry the actual strict-pullback and universal-property arguments.

## Review by Q77

I checked the node files against delivery-errors B--E with their statements and the ILO text open. The only new node is a self-contained theorem with no proof sketch, proof dependencies or implicit object. Its locally Noetherian fs scheme and log/chart notions come from `def-trf-fs-log-blowup`; its Zariski log structure is explicitly specified on that site with the same units axiom. Its mathematical conclusion is only chart existence. The record is unsplit, has complete blueprint provenance and genuinely executed search records. No Stacks tag is assigned to an assertion whose source is ILO; there is no new Stacks-tag duplicate requiring a fabricated citation.

For step 1, I checked that `lem-trf-zariski-fs-monoid-chart` supplies charts on Zariski opens, `def-per-strict-log-morphism` specifies the associated inverse-image log structure with the actual maps, and `lem-per-integral-chart-logification-thickening` gives the chart mapping bijection for an arbitrary scheme map and an arbitrary target log structure. The chart monoid is fs, hence finitely generated integral, exactly as that bijection requires. The final Zariski-origin conclusion for a global monoid chart is explicitly in `lem-trf-monoid-chart-characteristic-fan`. The overlaps agree by uniqueness fixing the pulled-back prelog sections and units. No abstract characteristic isomorphism is substituted for g's log map.

For step 2, I checked the statement of `lem-trf-monoid-chart-characteristic-fan`: it identifies ordinary and geometric characteristic stalks with the face-localized sharp monoid and specifies the induced comparison map. The local ring map sends the maximal ideal into the maximal ideal, so no chart nonunit can become a unit at the chosen point. Thus the same face is used on both sides, even when g is a closed immersion or is neither flat nor etale. The assertion about a Zariski sheaf map being an isomorphism is the elementary germ argument, with local inverses glued by uniqueness; no etale-stalk criterion is being misapplied to a Zariski sheaf.

For step 3, I checked the quotient-by-units and chart pushout clauses of `def-trf-fs-log-blowup`, not merely its ideal terminology. Local lifts of each of the finitely many characteristic generators give local log generators; multiplying by a unit does not change the generated ideal. On a chart these lifts are chart elements times units, so coherence has exactly the required finite nonempty chart witnesses. Applying the same computation after g gives the actual inverse-image ideal equality. This is a finite-generator calculation from the cited definition, not an unsplit theorem hidden under “coherence is clear”.

For step 4, I read `lem-trf-coherent-log-ideal-chart-construction` and used its stated existence of the saturated construction with the fs principalization property, not an argument inside its proof. Its locally Noetherian fs hypothesis holds for both V and W, and strict pullback preserves the same finite nonempty generator sets. `def-trf-fs-log-blowup` states the unique factorization for fs log test schemes. I additionally cited `lem-trf-log-ideal-chart-lifting-criterion`, whose statement explicitly imposes no Noetherian condition on the test T, so the Cartesian tests have not been silently restricted. The equation of pulled-back ideals is proved on images of the original sections. Principalness, rather than a claim about underlying ordinary ideal sheaves, gives the factorization.

For step 5, the only outside fact is precisely the universal property in `def-trf-fs-log-blowup`. Pullback of a principal monoid ideal stays principal because the image of the generator generates; composition of generated-image ideals is written out. Two applications of uniqueness give both projections and uniqueness for the requested Cartesian square. This argument works for arbitrary fs T, including those not locally Noetherian, because the chosen blowup's universal property and the preceding lifting criterion have that scope.

For step 6, I checked that `lem-trf-coherent-log-ideal-chart-construction` supplies the actual saturated fraction charts for both bases, and `lem-trf-log-ideal-affine-atlas-gluing` explicitly states compatibility with every ring map, including pulled-back log structures and overlaps. Therefore no flatness or etaleness of g is required. The old log-ideal generators are the same finite E in the shared P chart. The saturated monoids are formed inside the same group completion, and the map fixes them. The arbitrary-base chart mapping bijection in `lem-per-integral-chart-logification-thickening` then identifies the chart log structure with the associated inverse image, which is strictness. Uniqueness from step 4 identifies this local construction with the previously specified g', so the proof establishes strictness of that map. The chart covers are etale covers, as allowed by the definition of fs structures and coherent centers.

For step 7, I checked that `def-trf-fs-log-blowup` gives uniqueness as log morphisms, not merely as scheme maps. Both the identity comparison and the composite comparison have the same base map and the same composite log-section maps. The generator description proves the needed equality of pullback centers; uniqueness therefore gives the two coherence equations.

I tested the statements on the trivial log structure (P=0 and whole ideal), on an already principal ideal (the identity satisfies the universal property), on the empty underlying scheme (all assertions are local or have the unique empty map), and on a strict map to a closed point of a boundary (P=N with a nonunit sent to zero, so the face remains unchanged). For P=N^2 and E={(1,0),(0,1)}, even after a nonflat specialization both blowups have the same saturated fraction monoids and tensor base change is valid; the argument does not import the false general assertion that ordinary scheme blowups commute with arbitrary base change. Empty monoid centers are excluded exactly by the hypotheses, while a whole-monoid center is allowed and produces the identity case. For the new node, a unit-only log structure has chart P=0; a non-split etale structure lacking Zariski origin is outside its hypotheses, so no Zariski splitting of monodromy is asserted.

I also checked candidate dependency reachability before using the construction, atlas, and arbitrary-base chart nodes: none depends on this item. Each citation quotation was taken verbatim from the corresponding node statement and checked by membership. All seven steps are under 1200 characters, so there are no non-elementary steps over 2000 characters hiding an auxiliary lemma. The missing chart-existence theorem was separated instead of being cited as an unstated “standard” fact. The substantive corrections were to the initially implicit chart pullback argument, the exact-section nature of the characteristic map, and the unrestricted fs tests; no mathematical statement was weakened.

## Unfinished work

None in this one-level split. The new chart-existence theorem is intentionally statement-only for a later worker, as required. No Lean was written and no compiler, Lake or build tool was run. Repository and launcher files were read only; all writes are confined to this sandbox. Validation and delivery use the prescribed server tools.
