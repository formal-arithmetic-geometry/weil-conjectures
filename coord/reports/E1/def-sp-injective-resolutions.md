Files written:

- `dag/nodes/sec-abelian-varieties/def-sp-injective-resolutions.json`: parent definition, split status, corrected statement dependency, and split report.
- `dag/nodes/sec-abelian-varieties/def-sp-enough-injectives.json`: definition, Mathlib leaf (`CategoryTheory.EnoughInjectives`, `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean:64`).
- `citations.json`: empty, because the item is a definition with no proof steps.

Attachments: none. No sorry-free project declaration tagged `(blueprint: def-sp-injective-resolutions)` or stating this combined definition was found in `WeilConjectures/`.

WANTED: none.

## Not duplicates

`def-sp-enough-injectives` vs `lem-sp-grothendieck-enough-injectives`: the new node defines the notion of a category having enough injectives, while the existing node states the theorem that every Grothendieck abelian category has that property.

The imported parent incorrectly listed `def-sp-grothendieck-abelian` as a statement dependency even though its definition only assumes an abelian category with enough injectives; that unused dependency was removed. The reviewer note correctly identified that “enough injectives” had no definition node. The new node supplies it and matches Mathlib's `EnoughInjectives` presentation field.

## Review by E1

I read the imported parent node and its blueprint source path, the chapter and unit records, the existing `def-sp-abelian`, `def-sp-grothendieck-abelian`, and `lem-sp-grothendieck-enough-injectives` nodes, and the Mathlib sources `CategoryTheory/Preadditive/Injective/Basic.lean` (definitions at lines 32 and 64) and `CategoryTheory/Abelian/Injective/Resolution.lean` (resolution structure). The parent is a definition, so it has no proof steps or citation quotes. Its only nonlocal notion is “enough injectives”; the new child states that notion self-containedly as monomorphisms into extension-injective objects and is therefore the only needed statement dependency. The old Grothendieck dependency was checked against the parent text and removed because it is not used to state the definition.

For the child, LeanFinder and Loogle both returned `CategoryTheory.EnoughInjectives` and its `presentation` field; grep located the class at `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean:64`. LeanSearch was unavailable and is recorded as such. The Mathlib declaration says exactly that every object has an injective presentation, i.e. an injective object and a monomorphism into it. I checked the edge cases conceptually: a zero category satisfies the definition via its zero object, while a category lacking an injective envelope does not. No existing DAG node defines this notion; the only matching existing node is the separate Grothendieck existence theorem, recorded in `## Not duplicates`.

## Second reading by E1

- Parent statement: checked against blueprint node `def-sp-injective-resolutions`; agrees hypothesis by hypothesis, and is a definition with no proof steps.
- Parent proof: no steps, so there are no uncited dependencies or elementary-step claims to repair.
- `def-sp-enough-injectives` statement: checked against the parent clause and Mathlib `Injective` (lines 32–33) plus `EnoughInjectives` (lines 62–65); exact one-line specialization to abelian categories.
- `def-sp-enough-injectives` form: statement-only, self-contained, TeX is written once, `[def-sp-abelian]` is cited, and the source and Mathlib search records are present.
- Existing-node search: checked `dag/nodes` for the tag and the Grothendieck theorem; no duplicate definition of “enough injectives” exists.
- Edge cases: the zero category has enough injectives via its zero object; a category without an injective target fails the condition; the definition is independent of cochain degree (`n=0,1`).
- Changes: no mathematical node or citation changes were needed after the second reading; this section records the checks and confirms the worker’s removal of the unused Grothendieck dependency.

