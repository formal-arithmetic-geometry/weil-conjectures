1. Files written:

   - `dag/nodes/sec-curve-estimates/def-sc-topological-abelian-cohomology.json`: definition, no new Mathlib leaf.

2. Attachments: none.

3. WANTED: none.

4. The imported item was an unsplit definition. I retained its statement and corrected its source note to distinguish Cohomology Section 01DZ from the separate sites-cohomology lemmas 03FD and 03F3. I added `def-sp-injective-resolutions` to the statement dependencies because the definition explicitly uses right derived functors computed in an abelian category with enough injectives. No proof steps or new nodes are appropriate for this definition; the existing Zariski cohomology definition supplies the scheme specialization.

5. Nothing remains unfinished.

## Review by M1

I read the item node and the parent blueprint context in `lem-sc-pic-proper-ntorsion`, including the use of arbitrary abelian-sheaf cohomology in Lemma 09NY. I checked the source label against Stacks Cohomology Section 01DZ (`section-cohomology-sheaves`), and checked the scheme clause against the existing `def-sc-zariski-site` and `def-sc-zariski-cohomology` statements. The existing `def-sp-injective-resolutions` statement defines the injective-resolution notion used by “right derived functor,” so it is now a direct statement dependency. Since this is a definition, there are no proof steps and therefore no step citations; `citations.json` is the required empty list. I searched the Lean source for the item id, its key phrases, and the blueprint tag and found no declaration, with or without `sorry`. Mathlib searches already recorded in the item found no general topological abelian-sheaf cohomology declaration; the definition remains non-Mathlib.
