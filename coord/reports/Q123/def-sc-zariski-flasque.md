1. Files written:

- `dag/nodes/sec-smooth-purity/def-sc-zariski-flasque.json`: definition, Mathlib leaf (`TopCat.Sheaf.IsFlasque`), no new nodes.
- `citations.json`: empty because a Mathlib leaf has no proof steps.

2. Attachments: none. `TopCat.Sheaf.IsFlasque` is declared in Mathlib, so this is a Mathlib leaf rather than a project attachment.

3. WANTED: none.

4. What was wrong or changed: the imported node was still marked `unsplit` and had only an old text-search record. The Mathlib source defines the same notion generically as the presheaf predicate that every restriction map is epi (`Mathlib/Topology/Sheaves/Flasque.lean:48,70`); for abelian-group-valued sheaves, epi means surjective by `AddCommGrpCat.epi_iff_surjective`. I changed only the sandbox copy to status `mathlib`, recorded the declaration and source line, filled `blueprint.same_as` with the empty list, and recorded the required searches. A second wording of the search was run for both semantic and name searches; the direct match was verified by reading the source.

5. What I could not finish: nothing.

## Review by Q123

I read the target node, its blueprint source, the unit and chapter records, and `Mathlib/Topology/Sheaves/Flasque.lean`. The source’s `Presheaf.IsFlasque` class requires `Epi (F.map i)` for every inclusion of opens, and the sheaf abbreviation at line 70 applies that class to the underlying presheaf. In `AddCommGrpCat`, these component epimorphisms are precisely surjective group homomorphisms, so the Mathlib declaration matches every clause of the target definition. I also searched the project source for a tagged declaration and found none under `WeilConjectures/`; the only direct declaration is Mathlib’s. I checked the blueprint search for duplicates and found no other blueprint node stating this definition. The recorded LeanFinder, Loogle, LeanSearch, and source-grep searches include a second phrasing where the first semantic/name query did not directly identify the declaration. Since this node is a Mathlib leaf, there are no proof steps or cited-node quotes to add.
