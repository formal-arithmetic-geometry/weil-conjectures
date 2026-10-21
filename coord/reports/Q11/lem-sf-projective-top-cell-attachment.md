## Worker report

Files written: `dag/nodes/sec-six-functors/lem-sf-projective-top-cell-attachment.json` (statement, split; not a Mathlib leaf), `citations.json`, and this report. There are no new nodes and no new Mathlib leaves. `searches.jsonl` records the search command's results. The sandbox initially held only dispatcher brief markers, so this is a first split copied from the current repository item; all inherited searches, source, blueprint provenance and other fields were retained.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag, top-cell and attachment terminology, and projective-complex notions found no declaration proving all clauses. `DerivedCategory.Q_map_surjective_of_projective` in `WeilConjectures/Algebra/Homology/DerivedCategory/ProjectiveHom.lean:35` proves the representative ingredient only. The existing DAG leaf `lem-pc-ring-derived-map-representative` already states the general abelian-category result, so it is reused.

WANTED: none.

The original item supplied no proof. Its phrase “last differential is g with the sign fixed” was ambiguous. With the cone differential and cochain shift recorded in its definition dependency, the evident degree-b identification yields minus g. I made that formula explicit and gave the degree-b negation identifying it with the complex having differential plus g. This clarifies the convention and preserves the conclusion that the cone represents M, all hypotheses, and the degree and freeness assertions. There is no statement dispute or source error.

Read the chapter and unit records, GOAL.md, the three route levels of SETUP.md, and delivery-errors B–E (including the duplicated historical sections). The unit is the interface-discharge remark with no proof steps; this item is a generic homological algebra input under its recorded local-projective-model ancestry. It does not replace the unit or chapter route. Blueprint searches for projective complex, bounded-above, connecting morphism, mapping cone, and top projective found no equivalent imported node. The current main-20261015 ancestor proof's evaluation-naturality paragraph was read; the existing precise from.place and via chain are retained, and same_as remains empty.

Mathlib searches used the prescribed msearch.py command (two semantic phrasings, Loogle, grep, and LeanSearch); all were available in this run. Hits give mapping cones, cone triangles, short-exact-sequence triangles and projective resolutions, rather than the full top-term realization by a one-line specialization. I read DerivedCategory/KProjective.lean:43, HomotopyCategory/KProjective.lean:113, HomotopyCategory/MappingCocone.lean:32 and its maps, the mapping-cone triangle definition in HomotopyCategory/Pretriangulated.lean, and the localization triangulated structure in DerivedCategory/Basic.lean. No Mathlib leaf was invented for a combination needing a representative, two rotations, comparison of triangles and support calculation.

Nothing remains unfinished in this one-level split.

## Not duplicates

No new nodes. Whole-DAG searches for 064B, projective bounded-above representatives, cone triangles, 014A and 014B identified the existing general representative leaf, the existing triangle-morphism isomorphism leaf and the two definition leaves used here. The projective-cohomology-split-model sibling has stronger geometric hypotheses and additional cohomology-splitting clauses; there is no reason to cite it instead of the existing arbitrary-abelian-category representative leaf.

## Review by Q11

I read Stacks proetale.tex Tag 09C3, label lemma-local-structure-constructible-complex, particularly its final induction paragraph: the connecting map becomes a top differential and the extended complex represents the original object. For the general ringed-site version I read derived.tex Tag 064B (lemma-morphisms-from-projective-complex), Tag 014E (definition-cone), the distinguished cone convention at Tag 014Q, and Tags 014A/014B for triangle comparison. There are no new nodes needing separate sources.

Step 1 uses the precise abelianity assertion in def-weil-sheaf-of-modules-category: the given universe-smallness hypothesis is exactly what it needs. The full statement of lem-pc-ring-derived-map-representative is for any abelian category, not merely modules over a ring despite its name. Its source complex is bounded above and projective, exactly as assumed here; its target is unrestricted. Surjectivity supplies the desired homotopy class, whose chain-map representative gives delta. No unjustified enough-projectives hypothesis, or projectivity of arbitrary finite free sheaves, is asserted.

Step 2 uses only the definition of a chain map in def-weil-abstract-derived-category and the single-term support. I wrote the equation in degree b-2 rather than assuming any constancy of matrix entries. The remaining component equations are zero.

Step 3 uses the actual cone-triangle and shift clauses of def-weil-abstract-derived-category, TR2 and TR3 as explicitly stated in def-weil-triangulated-category, and the full isomorphism criterion of lem-sf-triangle-morphism-iso. Two rotations produce the SAME connecting map delta as first arrow, and the displayed subsequent arrows have their minus signs. Thus identity maps on its endpoints really commute; TR3 gives the third component, and two identity components meet the isomorphism criterion. Shifting its isomorphism down identifies M with the localization of the shifted cone. This does not presume functorial cones or uniqueness of the third component.

Step 4 is a component calculation from the recorded cone and shift definitions: D in degree q is Q in degree q plus T in degree q-1, and the negative shift negates the cone differential. I checked the order of summands, the sign of the last differential, and the explicit degree-b negation. This is an elementary calculation, not an uncited comparison theorem.

Step 5 is the finite-list and zero-term observation from step 4. I checked P=0, Q=0, b=a+1, and vanishing individual Q terms, as well as a nonzero two-term example with a=0, b=1, Q^0=P a free module and g identity: the differential is minus identity in the evident coordinates and the cone is acyclic as expected. Finite free here means a finite direct sum of the ring sheaf, including the empty sum. No free-sheaf projectivity is inferred on an arbitrary site.

Every proof citation was checked against its node's statement, not its proof. citations.json contains a verbatim statement quote for every step-use pair. All non-elementary inputs are existing cited nodes; elementary steps contain the calculation rather than outsourcing a clause to a new lemma. No step exceeds 2000 characters. No SGA source, compiler, build, repository write, or git command was used.
