# Stage-1 report

1. Files written:
   - `lem-pc-fp-complex-descent.json`: split statement.
   - `lem-pc-fp-module-map-descent.json`: unsplit statement-only node; Mathlib searches found no match.
   - `citations.json`: one verbatim citation for step 2.
2. Attachments: none.
3. WANTED: none; `literature/stacks-project/limits.tex` is present.
4. The imported item had no proof. The source route in Lemma 32.10.2 (Tag 01ZR) requires finite-presentation descent of terms, differentials, and relations, so I added the smaller module-and-map statement rather than moving the whole item into a new node. The existing flat-complex node depends on this item, so it was not used as a citation.

## Not duplicates

`lem-pc-fp-module-map-descent` vs `lem-pc-fp-complex-descent`: the helper descends one finite module-and-map diagram; the item assembles all bounded terms, differentials, and square-zero relations into a complex.

`lem-pc-fp-module-map-descent` vs `lem-pc-flat-bounded-complex-descent`: the existing node adds flatness and depends on the item, so it is not the same statement and cannot be cited without a cycle.

`lem-pc-fp-module-map-descent` vs `lem-pc-finite-flat-proper-support-descent`: the helper descends one module map without flatness or proper-support conclusions; the existing node descends a bounded complex and adds both properties.

`lem-pc-fp-module-map-descent` vs `lem-pc-noetherian-approximation-data`: the helper is only finite module-map data; the existing node also descends the scheme, proper supports, and a perfect object.

`lem-pc-fp-relation-descent` vs `lem-pc-finite-flat-proper-support-descent`: the relation node only makes finitely many equations hold at a later stage; the existing node descends a whole complex with flatness and proper support.

`lem-pc-fp-relation-descent` vs `lem-pc-noetherian-approximation-data`: the relation node is only the square-zero relation step; the existing node also descends the scheme, flat module complex, proper supports, and perfect object.

`lem-pc-fp-relation-descent` vs `lem-pc-fp-complex-descent`: the relation node assumes the module maps have already been descended and only asserts eventual validity of finitely many equations; the item constructs the entire bounded complex and its base-change isomorphism.

`lem-pc-fp-relation-descent` vs `lem-pc-flat-bounded-complex-descent`: the relation node has no flatness or proper-support conclusion and is a finite relation substep, while the existing node proves the stronger flat-complex descent and depends on the item.

## Review by E1

I read the item source `literature/stacks-project/limits.tex`, Lemma 32.10.2 (Tag 01ZR), and checked the imported statement against its hypotheses: affine inverse system, Noetherian affine stages, finitely presented scheme, and bounded finitely presented module complex. I also read the existing `lem-pc-flat-bounded-complex-descent` and `lem-pc-flat-module-descent` nodes; the former depends on this item and the latter concerns eventual flatness, so neither can supply finite-presentation descent here.

Step 1 is elementary: boundedness leaves finitely many terms, maps, and equations. Step 2 cites `lem-pc-fp-module-map-descent`, whose statement supplies exactly descent of finitely presented modules and maps with compatible base-change isomorphisms. Step 3 cites `lem-pc-fp-relation-descent`, whose statement supplies eventual validity of the specified composite-zero equations. Step 4 is elementary assembly. I checked the small cases of a zero-length complex and a one-term complex: the first has no differentials or relations, and the second uses only one descended module. Both new nodes are statement-only by design, have complete hypotheses, and record all required searches; no Mathlib declaration states the needed geometric inverse-limit descent.

## Second reading by E1

- Item statement: checked against Limits, `limits-lemma-descend-modules-finite-presentation`, Tag `01ZR`; the inverse-system, finite-presentation, bounded-family, and base-change hypotheses and conclusion agree.
- Step 1: checked against the explicit bounded-family/differential definition now in the item; finite support leaves finitely many modules, maps, and equations, so elementary is correct.
- Step 2: checked against `lem-pc-fp-module-map-descent`; its Tag `01ZR` statement supplies finite-presentation descent of each module and differential with base-change identifications.
- Step 3: checked against `lem-pc-fp-relation-descent`; its Tag `01ZR` statement supplies eventual equality of each finite list of composites.
- Step 4: checked from the termwise identifications and the displayed differential compatibility; finite support makes the assembly elementary.
- `lem-pc-fp-module-map-descent`: checked against Limits, `limits-lemma-descend-modules-finite-presentation`, Tag `01ZR`, including its module-map clause; the statement is self-contained and cites the quasi-coherent-module definition.
- `lem-pc-fp-relation-descent`: checked against the equality clause of the same Tag `01ZR` lemma; finite collections reduce to a common later stage, and all module notions are defined by cited nodes.
- New-node checks: all three are statement-only; TeX is single-escaped in JSON; searches are recorded in `searches.jsonl`; no Mathlib declaration matched; no duplicate node states this finite module-map/relation data.
- Small cases checked: the empty and one-term complexes have no nontrivial differential relation; a zero module makes every listed relation immediate.

Changes made: added the existing quasi-coherent-module definition to all new-node dependencies; made the complex data (finite support, differentials, and square-zero equations) explicit; corrected each source place to the Stacks label and Tag `01ZR`; retained the original proof route and citations.
