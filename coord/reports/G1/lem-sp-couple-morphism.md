# Stage 1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-couple-morphism.json` — item, split.
- `dag/nodes/sec-abelian-varieties/lem-sp-derived-couple-functoriality.json` — statement, unsplit, Mathlib searches found no match.
- `citations.json` — verbatim dependency quotes for all proof steps.

2. Attachments: none.

3. WANTED: none.

4. Problems found: the source tree contains no declaration tagged `(blueprint: lem-sp-couple-morphism)`, and no declaration matching the notion by keyword search. The imported proof was one paragraph; I separated its non-elementary derived-couple functoriality into one new node. The remaining filtration and associated-graded arguments are direct applications of the stated image filtration and quotient definitions together with the convergence theorem. No statement was changed.

## Review by G1

I read the item source in `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/lem-sp-couple-morphism.md`, the exact-couple definition, the convergence definition, the half-plane convergence theorem, and the filtration definition. I also searched the full Lean source for the item tag and for exact-couple/spectral-sequence morphism names; no project declaration exists. For Step 1, the new node states exactly the needed derived-couple maps, page compatibility, and preservation of the limiting cycles and boundaries. For Step 2, the half-plane theorem states the image filtration formula used, while the exact-couple definition supplies the commuting structure maps; the inclusion under every power of alpha is the one-line image argument. For Step 3, the convergence theorem states the associated-graded identification, the new node states the E-infinity map, and the filtration definition states graded pieces as the quotient used to identify the induced map. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item and new node; LeanSearch was unavailable and is recorded as such. I checked JSON validity, ran `tools/check_dag.py`, and recorded every cited statement verbatim in `citations.json`.

5. Unfinished: the project-wide check reports only pre-existing reach and route warnings; no item-specific error was found.

## Not duplicates

lem-sp-derived-couple-functoriality vs def-sp-exact-couple: the existing node defines one exact couple and its derived construction, while the new node asserts functorial maps between two couples and their pages.
lem-sp-derived-couple-functoriality vs lem-sp-exact-functor-couple: the existing node concerns applying an exact functor to a couple; the new node concerns an arbitrary morphism between two couples in the same abelian category.
lem-sp-derived-couple-functoriality vs lem-sp-derived-couple-exact: the existing node proves that one derived couple is exact and describes iteration, while the new node proves that a morphism of couples induces compatible maps on those derived couples and on E-infinity.
lem-sp-derived-couple-functoriality vs thm-sp-half-plane-convergence: the existing theorem proves stabilization and associated graded convergence under half-plane hypotheses; the new node proves naturality under morphisms without those hypotheses.

## Second reading by G1

- Item statement: checked against the blueprint lemma and the exact-couple, filtration, and half-plane-convergence nodes; repaired the previously implicit definition of a morphism of exact couples and made the total-degree quantifier explicit.
- Step 1: checked against the helper-node statement and Stacks Tags 011R and 011T cited by the split; the cited statement supplies derived maps, page differentials, and the $Z_\\infty/B_\\infty$ map.
- Step 2: checked against `thm-sp-half-plane-convergence` and `def-sp-exact-couple`; the image-filtration inclusion is a short consequence of the explicitly stated commuting square and its powers.
- Step 3: checked against `thm-sp-half-plane-convergence`, `def-sp-filtration`, and the helper node; restriction to subobjects and passage to quotients gives the associated-graded map.
- `lem-sp-derived-couple-functoriality`: checked B1--B7, the derived-couple source clauses, and Mathlib searches; repaired self-containment by spelling out all three commuting equations for the couple morphism.
- No small-case counterexample arose: zero objects and zero maps satisfy the equations, and the construction specializes correctly in a field-valued abelian category.

Changes made: added the missing definition of a morphism of exact couples to the item and helper statements; added the required total-degree quantifier; retained the existing proof split and citations because their quoted node statements remain exact.
