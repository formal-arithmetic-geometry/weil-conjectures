# Stage 1 report: def-sp-image-filtration

## Files written

- `dag/nodes/sec-abelian-varieties/def-sp-image-filtration.json`: definition, no new nodes, Mathlib searches recorded, status `split`.
- `citations.json`: empty because a definition has no proof steps.

## Attachments

None. No sorry-free project declaration tagged `(blueprint: def-sp-image-filtration)` or stating this definition was found in `WeilConjectures/`.

## WANTED

None.

## What I checked

The item source is the blueprint node `def-sp-image-filtration`, order 508, whose statement defines the image filtration of a filtered object `(A,F)` along a morphism `A -> B` in an abelian category by `F^n B = im(F^n A -> B)`. I read the prerequisite node statements `def-sp-filtration` and `def-sp-abelian`; they provide exactly the filtered object and abelian-category notions used in the item. The item is therefore a definition split with those two statement dependencies and no proof theorem.

I searched the whole blueprint with `tools/blueprint_refs.py search` for “image filtration”, “012E”, and the defining key words. The only matching blueprint node is this item, so there is no duplicate node to cite or create. I searched the project Lean source for the item id, its blueprint tag, and image-filtration terminology; there is no project declaration for this definition. Mathlib searches were run twice each with LeanFinder, Loogle, and source grep, plus LeanSearch (which was unavailable); they found only the general abelian image functor or unrelated filtered constructions, not this filtered-object image-filtration definition.

## Review by J1

I checked that the item statement introduces all of its objects and that each referenced notion is supplied by the cited prerequisite node: `def-sp-filtration` defines filtered objects and `def-sp-abelian` defines the ambient abelian category. Since the item is a definition, there are no proof steps, no proof dependencies, and no non-elementary facts requiring citation; `citations.json` is consequently empty. I also checked the small edge cases conceptually: for the zero morphism every image filtration term is zero, and for an identity morphism the induced filtration is the original one, matching the stated recipe. I removed the section-number text `12.23.4` from the parenthetical source note because the delivery preflight requires every quoted section number to be carried by a cited node or source; the Stacks tag `012E` and its formula remain. No mathematical statement or source error was found, and no new node was warranted.

## What was wrong or incomplete

Nothing in the item or blueprint needed correction. The literature checkout does not contain the referenced blueprint Markdown path, but the imported node contains the complete statement and source metadata used here.

## What I could not finish

Nothing. The required dry run is to be performed from the group delivery sandbox after this report is reviewed.

## Second reading by J1

- Item statement: checked against blueprint node `def-sp-image-filtration` and Stacks Tag 012E, Definition 12.23.4; the arbitrary-morphism image recipe correctly specializes to filtered differential-object homology, with no hypotheses added or dropped.
- Definition dependencies: checked `[def-sp-filtration]` and `[def-sp-abelian]`; each cited notion is defined by the cited node, and the ambient abelian-category hypothesis is explicit.
- Edge cases: checked the zero object and zero morphism (all terms are zero), identity morphism (the original filtration is recovered), and field/empty cases; the definition remains well-formed.
- Proof and citations: this is a definition node with no proof steps or proof dependencies, so `citations.json` is correctly empty.
- New-node audit: no new child nodes exist; no duplicate, elementary, restatement, or Mathlib leaf was introduced. The blueprint search and Mathlib searches recorded by the worker were inspected.
- Form checks B1-B7: statement-only node, self-contained objects and hypotheses, definition-node references present, TeX written once, and source identified by Stacks tag and label.
- Change made: verified the statement contains only the stable Tag 012E source reference; no section-number text remains. The source formula and general definition are unchanged.
