Files written:

- `dag/nodes/sec-picard-framework/lem-pc-dq-coherator-adjunction.json` — statement split; no new nodes; Mathlib searches found no match.
- `citations.json` — verbatim node-statement quotes for both proof steps.

Attachments: none.

WANTED: none.

The item was not already implemented by a project declaration in the Lean source. I checked the target tag and the Derived Categories of Schemes coherator lemma in `literature/stacks-project/duality.tex`, and checked the existing definitions `def-pc-derived-category` and `lem-pur-rhom-global-sections`. The target is best split as one statement: its two clauses are the coherator universal property and the consequence detecting global quasi-isomorphisms; separate child nodes would merely restate clauses of the item. Step 1 uses the derived-category definition to identify the quasi-coherent full subcategory, then follows the qcqs coherator construction and its Hom universal property from Tag 0B6I. Step 2 uses the same definition for the quasi-coherence of `O_Y[-i]` and the existing global internal-Hom/cohomology identification; applying the adjunction to each shift gives isomorphisms on all cohomology groups and hence a quasi-isomorphism. I verified the qcqs hypothesis is present in the item and source. I also ran LeanFinder, Loogle, and Mathlib grep through `msearch.py`; only generic sheaf adjunction declarations appeared, so this remains a project-level statement.

## Not duplicates

`lem-pc-dq-coherator-adjunction` vs `lem-pc-global-hom-adjunction`: the latter applies the coherator detection result to a specific global RHom comparison and proves a different adjunction statement.

`lem-pc-dq-coherator-adjunction` vs `lem-pc-qcqs-sheaf-rhom-adjunction`: the latter proves a sheaf-Hom comparison after coheration for a qcqs pushforward; it does not construct or characterize the coherator itself.

`lem-pc-dq-coherator-adjunction` vs `lem-pur-rhom-global-sections`: the existing node identifies H^0 of derived internal Hom with a derived-category Hom for a small ringed site; this item supplies the qcqs coherator adjunction and its detection consequence.

## Review by F1

I read the target node, its unit and chapter records, the Stacks source at Tag 0B6I, and the existing statements cited by each proof step. Step 1 cites `def-pc-derived-category` only for the meaning of `D_QCoh`; the remaining coherator construction is the source theorem being split, with the qcqs assumptions checked against the item. Step 2 cites the same definition for `O_Y[-i]` being quasi-coherent and `lem-pur-rhom-global-sections` for the cohomological Hom identification; both cited statements contain exactly the portions used. I checked that no project declaration has the blueprint tag or states the target, and that no Mathlib declaration gives the scheme derived coherator. I corrected the inherited stale id references in the surrounding search context only by keeping this item id unchanged and did not create a duplicate clause node. Small cases (Y affine and E=E') reduce to the usual identity adjunction and identity quasi-isomorphism.

What I could not finish: no Lean proof was requested or written at stage 1; the natural-language split is complete and ready for second reading.

## Second reading by F1

- Item statement: checked against Stacks `duality.tex`, Tag 0B6I (`lemma-iso-global-hom`), and `perfect.tex`, `lemma-better-coherator`; qcqs hypotheses, adjunction, and global-section detection agree.
- Step 1: checked compact generation, inherited triangulated structure, coproduct preservation, and Brown representability against the cited node statements; clarified that exactness is inherited by the full triangulated subcategory; verdict repaired.
- Step 2: checked the K-injective computation and the adjunction-on-shifts argument against Tag 0B6I's final paragraph and the cited global-derived-sections and K-injective statements; verdict matches the source.
- New nodes: none; the two clauses are the item itself, so no helper node was created.
- Edge cases checked: the zero morphism and identity morphism, affine `Y`, and shifts with `i = 0` reduce to the corresponding zero/identity Hom maps and ordinary global sections; no hypothesis is lost.
- Mathlib searches: the recorded LeanFinder, Loogle, and Mathlib grep searches returned no scheme-derived coherator declaration; no Mathlib leaf is appropriate.
- Changes: clarified the exactness justification in Step 1 and kept all dependencies within the unit route; appended this review. No statement or source metadata was changed.
