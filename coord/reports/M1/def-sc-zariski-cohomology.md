# Stage 1 report: def-sc-zariski-cohomology

## Files written

- `dag/nodes/sec-smooth-purity/def-sc-zariski-cohomology.json`: item marked split; no new nodes.
- `citations.json`: empty because the item is a definition with no proof steps.

## Attachments

None. No exact sorry-free project declaration tagged `(blueprint: def-sc-zariski-cohomology)` or stating this definition was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED

None.

## What was wrong

The imported item was not attached to Lean because no matching declaration exists. Its statement already introduces the cohomology convention and cites the existing `def-sc-zariski-site` and `def-weil-pbc-kinjective-resolutions` nodes; no additional child node is needed for a one-level split of a definition. The blueprint source path is retained from the imported node, although that generated markdown file is not present in this checkout.

## Not duplicates

No new nodes were created, so there are no duplicate pairs.

## Review by M1

I read the item node, the `sk-prop-sf-cbc` unit record, the `sec-smooth-purity` chapter record, and the existing statements of `def-sc-zariski-site` and `def-weil-pbc-kinjective-resolutions`. The item says that for an abelian sheaf on the small Zariski site, cohomology is the right derived functor of global sections, equivalently computed from the section complex of an injective resolution; those are exactly the notions supplied by its two statement dependencies. Because this is a definition, there are no proof steps and `citations.json` is empty.

I searched the project source by the item id, blueprint tag, and Zariski/cohomology terminology; no exact declaration exists. I ran the required Mathlib searches: LeanFinder returned only generic `CategoryTheory.Sheaf.H` and related infrastructure, Loogle returned no hits after an identifier warning, grep returned generic Zariski/cohomology files without this definition, and LeanSearch was unavailable. Thus the item is not a Mathlib leaf or a Lean attachment. I checked edge cases conceptually: for a point the definition is ordinary derived global sections, and for the empty scheme it still defines the same derived-functor convention. No hypotheses or clauses were changed.

## Second reading by M1

- Item statement: checked against the imported blueprint definition and the existing `def-sc-zariski-site`; the repaired statement now introduces the scheme, the abelian-sheaf category, the global-sections functor, and the injective-resolution computation explicitly.
- Proof steps: there are no proof steps because this is a definition; `citations.json` remains correctly empty.
- New nodes: there are no new nodes; the item remains a one-level definition split.
- Existing dependencies: checked `def-sp-abelian`, `def-sp-left-exact-additive`, `def-sp-injective-resolutions`, and `lem-weil-pbc-site-sheaves-enough-injectives`; these state the category, derived-functor, injective-resolution, and enough-injectives facts used by the repaired statement. The prior `def-weil-pbc-kinjective-resolutions` dependency was removed because it concerns etale module sheaves and does not state the ordinary Zariski abelian-sheaf convention.
- Edge cases: a point gives ordinary global sections in degree zero; the empty scheme has the zero global-sections functor, so the definition remains coherent in every degree.
- Blueprint and searches: the imported item's `blueprint.from` remains `null` as required for imported nodes, while `split_report.blueprint` names both defining places; the existing Mathlib search log was checked and no exact declaration was found.

Changes made: introduced `X` and `F` with their definition citations, replaced the mismatched etale K-injective dependency with the ordinary abelian-sheaf resolution dependencies, and recorded the blueprint places in the split report.
