# Stage-1 delivery: lem-trf-excellent-scheme-affine-cover

Group Q30; 2026-10-18 (local date; search logs carry their actual UTC timestamps).

## Files written

All node paths are under `dag/nodes/sec-trace-formula/` in this sandbox.

- `lem-trf-excellent-scheme-affine-cover.json`: statement, split; six proof steps, unchanged statement. No Mathlib match.
- `lem-trf-g-ring-affine-cover.json`: statement, unsplit; G-ring locality for affine covers (Stacks 0HA5). No Mathlib match.
- `lem-trf-j2-affine-cover.json`: statement, unsplit; J-2 locality on a locally Noetherian scheme (Stacks 07R4). No Mathlib match.
- `lem-trf-universally-catenary-affine-cover.json`: statement, unsplit; universal-catenarity locality on a locally Noetherian scheme (Stacks 02J9). No Mathlib match.

`citations.json` contains nine verbatim statement quotations, one for every use by every proof step. `searches.jsonl` is the unmodified msearch log. The per-query `*.search-*.txt` files retain the returned search outputs; `planned-searches.json` and `run_searches.py` record how those requests were issued. Scratch scripts are sandbox-only and are not node deliveries. No unit or chapter file was changed.

## Attachments

None. I searched the entire `WeilConjectures/` source tree in `/home/ubuntu/weil-src-slopmaster2` for the exact item id and for excellent, G-ring, J-2 and catenary terminology. The sole excellence-related occurrence is explanatory prose in `SixFunctors/Etale/Derived/Stability.lean:174`, not a declaration of this result. The component statements have no matching project declaration either. No upstream sorry declaration was treated as finished.

## Literature wanted

None. All mathematical sources used here are present in `literature/stacks-project/`.

## Findings and changes

The original item statement is correct; there is no statement dispute or change of hypotheses. It had no proof. I supplied the argument of Stacks 0HAB by separating the three property-locality inputs cited by its proof. I made the local Noetherian hypothesis explicit before applying 07R4 and 02J9. G-rings include Noetherianity, which supplies that part of excellence on the resulting affine ring.

The old Mathlib-search field included two entries explicitly saying that their requests had not run. I replaced that field with the actual searches made by this worker, with the exact query strings, returned names/counts and logged digests. All new-node search records contain the actual query output and a verdict. All services succeeded in this run. The initially broad G-ring grep also matched `Ring.ringCompute` and unrelated prose; I retained those real results and ran a narrower word-boundary query, which returned no hits.

The current main-20261015 blueprint statement and proof for `lem-trf-local-term-locality`, the historical ancestor, concern contracting local terms. The inherited ancestry passes through generic smooth-boundary preparation and projective inseparable spread/normalization. I retained this provenance and made the new nodes' `from.place` specify their component-locality purpose; I did not pretend that the current local-term statement itself asserts excellence. The unit `sk-i-curve-zero` and chapter `sec-trace-formula` were read and left untouched. This is an auxiliary commutative-algebra split within the inherited route.

The source of 07R4 writes `S` instead of `X` in the covering formula of clause (4). The new statement consistently uses its introduced scheme `X`; this corrects only the source's variable typo. No mathematical assertion is changed.

## Unfinished work

None for this one-level split. The three new locality statements intentionally have no proof and are unsplit queue items. No new Mathlib leaf is claimed; the existing `lem-weil-pbc-affine-opens-basis` leaf is reused.

## Not duplicates

I searched the whole DAG by the three tags (0HA5, 07R4, 02J9), source labels and property keywords, and ran `tools/blueprint_refs.py search` for those tags, G-ring, J-2, catenary and excellent. There is no existing node with any of the three component-locality statements; the tag searches found zero blueprint nodes. Searching excellent finds the two existing excellent-local-ring results `lem-exc-dvr-galois` and `lem-exc-punctured-curve-branches`, neither of which is an affine-cover criterion. No existing source-tag pair for a new node requires a duplicate explanation on the current shared snapshot.

The three new nodes are not clauses of the item: none has excellence as hypothesis or conclusion. They are independently applicable locality results for distinct ring properties and are precisely the non-elementary component facts called by the source's proof. No new node is an equivalent restatement of the whole item. The elementary conjunction assembly and local-Noetherian deduction remain proof steps; the open-cover consequence remains a step using an existing basis leaf.

## Review by Q30

I read Stacks `morphisms.tex`, Tags 0HAB (`lemma-locally-excellent`), 0HAA (`lemma-characterize-excellent`) and the quasi-excellent characterization preceding it. Its proof first passes the G-ring and J-2 conditions from charts to affine opens, then passes universal catenarity. The split follows exactly that argument. For the new G-ring node I read `properties.tex`, Tag 0HA5 (`lemma-locally-G-scheme`), including its preceding G-scheme definition and characterization: clauses (3) and (2) give its entire statement without assuming local Noetherianity in advance. For the J-2 node I read `morphisms.tex`, Tag 07R4 (`lemma-J`), its four equivalent conditions and proof: (4) implies (3) on a locally Noetherian scheme. For the universal-catenarity node I read `morphisms.tex`, Tag 02J9 (`lemma-universally-catenary-local`), its four conditions and proof: (4) implies (3), again with local Noetherianity. These nodes are statement-only; their sources are tags and actual TeX labels, not changing section numbers.

For step 1 I opened `def-exc-excellent-ring` and `pqf-def-locnoeth`. The former explicitly defines quasi-excellence as Noetherian, G-ring and J-2, and excellence as quasi-excellence plus universal catenarity. The latter explicitly defines local Noetherianity by an affine cover with Noetherian coordinate rings. Thus unwrapping the excellent input establishes all four ring predicates and local Noetherianity without invoking any permanence theorem. I also read the source definitions in `more-algebra.tex`, Tag 07QT (`definition-excellent`), and `properties.tex`, Tag 01OV (`definition-noetherian`).

For step 2 I reread the exact statement of the new `lem-trf-g-ring-affine-cover`: it takes the same scheme and the given affine cover with G-ring coordinate rings, and concludes the G-ring assertion for the arbitrary affine open V. The other cited node, `def-weil-pbc-g-ring`, explicitly includes Noetherianity in its G-ring definition; I checked this also in `more-algebra.tex`, Tag 07GH (`definition-G-ring`). Thus no theorem about preservation of regular formal fibres is silently inferred from a definition: the theorem is the new 0HA5 node, and only the Noetherian conjunct is extracted by definition.

For step 3 the exact statement of `lem-trf-j2-affine-cover` includes both the locally Noetherian hypothesis supplied by step 1 and the J-2 hypotheses on precisely the original affine chart rings. Its conclusion is J-2 for the arbitrary affine V. The J-2 meaning is explicitly defined in the cited `def-exc-excellent-ring`; no weaker regular-locus assertion is substituted. For step 4 I checked the corresponding hypotheses and conclusion in `lem-trf-universally-catenary-affine-cover`, using the universal-catenarity predicates obtained in step 1. Neither step assumes the cover is finite, the scheme separated, or intersections affine.

For step 5 I reopened `def-exc-excellent-ring`: combining the already established predicates is exactly its definition, so this is an elementary step, not an additional theorem-node. For step 6 I opened the existing statement of `lem-weil-pbc-affine-opens-basis`: it gives, for each x in an arbitrary open W, an affine open of X lying inside W. I read Stacks `schemes.tex`, Tag 01IT (`lemma-basis-affine-opens`) as well. Taking all such opens covers W; their structure sheaves are the same restrictions of the structure sheaf of X. The excellence obtained in step 5 therefore applies to those same coordinate rings. This does not assume an intersection of affine opens is affine.

I checked small cases: the empty scheme and empty affine open correspond to the zero ring, with vacuous prime and regular-locus conditions and valid Noetherianity; an empty open W has the empty cover. A single affine chart gives the usual affine case, while arbitrarily many charts and disconnected schemes require no finiteness or irreducibility. All three new statements allow empty V and are consistent with their source equivalences. Local Noetherianity is retained in both nodes whose sources require it.

Against delivery-errors B--E: each new node is a self-contained statement with its defining notions linked, and has no proof sketch or proof dependencies. I verified the existing definitions actually define G-rings, J-2, universal catenarity and local Noetherianity. The item statement is unchanged; the new statements are properly weaker inputs, not duplicate excellence claims. Mathlib queries were executed only through msearch, with two semantic phrasings per new node; no unavailable request is called a negative result. The general affine communication result `AlgebraicGeometry.of_affine_open_cover` was read at `Mathlib/AlgebraicGeometry/AffineScheme.lean:1034-1042`: it still assumes localization stability and finite basic-open descent for the chosen property, and supplies no G-ring/J-2/catenary theorem. The returned Noetherianity results give only one predicate. These are not exact matches or one-line specializations.

Every use in each proof step is backed by the statement quotation in `citations.json`; I used no construction hidden inside another node's proof. The only non-elementary facts are the three cited locality nodes and the existing affine-basis leaf. The remaining operations are extracting definition conjuncts, assembling them, and restricting the structure sheaf. No off-unit non-Mathlib statement is used: all new nodes inherit the item's unit, the two existing ring/scheme/local-Noetherian notions are definitions, and the basis result is a Mathlib leaf. Dependencies point down to these inputs, with no new node depending on the item. No step exceeds 2000 characters. No SGA 4/4½ route, coefficient-category identification, or Lean/build action is involved.

The preliminary server `review_split` check passed. The complete dry run and push follow after this report.
