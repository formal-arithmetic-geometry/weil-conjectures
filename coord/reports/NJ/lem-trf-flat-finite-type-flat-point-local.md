1. Files written:
- `dag/nodes/sec-trace-formula/lem-trf-flat-finite-type-flat-point-local.json` (item; split, no Mathlib match).
- `dag/nodes/sec-trace-formula/lem-trf-finite-type-flat-etale-neighborhood.json` (statement-only supporting node; no Mathlib match).
- `dag/nodes/sec-trace-formula/lem-trf-finite-presentation-module-descent-flat-local.json` (statement-only supporting node; no Mathlib match).
- `citations.json` (verbatim statement excerpts for every cited step).

2. Attachments: none.

3. WANTED: none.

4. What was checked: the item is not present as a sorry-free declaration in the Lean source. I read the full Stacks proof of Tag 05I7 (flat.tex, `lemma-finite-type-flat-at-point-local`) and the preceding Proposition 05I6. The first new node is exactly the stronger 05I6 neighborhood statement, with all scheme, finite-presentation, flatness, etale, fibre-product, and open-subscheme notions introduced through existing definitions. The second new node is exactly Algebra Tag 03C4(2), finite-presentation descent for modules under a faithfully flat ring map. I searched the whole DAG and blueprint for 05I6, 05I7, 03C4, and the relevant finite-presentation/descent phrases; no duplicate node or blueprint statement was found. For Step 1, the 05I6 node supplies the etale neighborhood and a finitely presented, base-flat pullback. For Step 2, I checked the cited etale definition gives flatness, the existing localization-flat node gives flatness after passing to stalk localizations, and the existing flat-local-faithfully-flat node gives faithful flatness. The stalk, fibre-product, tensor, and module-presentation definitions supply the affine pullback identification and the meaning of finite presentation. For Step 3, the new 03C4(2) node states exactly the descent implication used. I tested the statement on the identity map and on a field extension: the conclusion reduces respectively to the original finite presentation and ordinary faithfully flat descent. No source or hypothesis was silently changed, and no SGA source was used.

## Review by NJ
I read the item source and both supporting source passages directly. The item proof has three steps: the first cites only the 05I6 neighborhood statement; the second cites the definitions and existing lemmas needed for flatness, localization, faithful flatness, stalks, pullback and finite presentation; the third cites only the 03C4(2) descent statement. I checked each quote in `citations.json` against the exact node statement. The local map in Step 2 is local because it is the map on local rings at the corresponding point, and flat because an etale map is flat and localization preserves flatness; the existing faithful-flat node applies precisely to flat local maps of local rings. The two new statements are strictly stronger/supporting facts, rather than clauses restating the item. The Mathlib searches for the item and each new node were run with LeanFinder, Loogle, grep, and LeanSearch; the recorded results were read and none states either theorem.

5. What I could not finish: nothing.

## Not duplicates
lem-trf-finite-presentation-module-descent-flat-local vs lem-weil-pbc-faithfully-flat-descent-finite-module: the existing node states descent of finite generation (finite type) along a faithfully flat map, whereas the new node states descent of finite presentation, requiring finite generation of the kernel as well.
lem-trf-finite-presentation-module-descent-flat-local vs lem-weil-pbc-formal-glueing-finite-modules: the existing node is the multi-step formal-glueing theorem for a special product/localization faithfully flat algebra and uses finite-generation descent internally; the new node is the general finite-presentation descent theorem for an arbitrary faithfully flat ring map.
