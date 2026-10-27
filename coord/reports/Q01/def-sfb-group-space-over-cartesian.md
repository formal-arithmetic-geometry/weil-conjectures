# Stage-1 delivery: def-sfb-group-space-over-cartesian

## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-group-space-over-cartesian.json: existing definition; Mathlib match by one-line specialization of CategoryTheory.Over.cartesianMonoidalCategory. No new nodes.
- citations.json: empty list, since a definition/Mathlib leaf has no proof steps.
- searches.jsonl: four actual current searches; all returned successfully.

## Attachments

None under the brief's requirement that an attachment be in WeilConjectures/. Searches for the exact blueprint tag, groupSpaceOverCartesian, and the slice-over-B notion in that project found no such declaration. Sheaf/AlgebraicGeometry/GroupSpaceOverCartesian.lean:38 already registers AlgebraicGeometry.AlgebraicSpace.groupSpaceOverCartesian with the one-line body Over.cartesianMonoidalCategory B.obj; I read it as confirmation of the specialization, not as a qualifying attachment. Its upstream owner metadata remains unchanged.

## WANTED

None.

## Findings and changes

The item is a definition, not a proposition requiring a proof split. Its live status was split without a Mathlib match. The requested construction is already an abbreviation in Mathlib, even though registering it as a global instance is a project implementation choice. Changed status to mathlib and supplied the exact declaration, file and source lines. Retained the full statement and all three statement dependencies, as well as the earlier searches and blueprint/source/Lean metadata. No definition or target meaning changed, and no Lean was written or compiled.

Read Stacks spaces-groupoids.tex, Tag 043H (definition-group-space) and Tag 04TW (definition-pseudo-torsor): they use precisely fibre products over B for group multiplication and action. Read the newest blueprint under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, including _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This definition supports the inherited pseudo-torsor branch; it changes no unit step. Blueprint searches for cartesian monoidal (no match) and fibre products (23 unrelated matches) give no duplicate blueprint definition. The existing blueprint ancestor query returns None, agreeing with the inherited from.node null and its detailed from.place; these were retained rather than inventing an ancestor.

## Not duplicates

No new nodes were created. The existing lem-trf-space-fibre-products-etale-covers proves closure of algebraic spaces under sheaf fibre products and stability of jointly surjective etale families; it does not define a chosen cartesian monoidal structure on the whole slice of fppf sheaves. It remains a statement dependency for the restriction sentence.

## Review by Q01

I checked B through E against the actual node, source text and Mathlib declarations. There are no new statements, hidden claims, proof steps, long steps, off-unit proof citations, or copied clauses disguised as new nodes. Consequently C1/C4 proof-step quotes are vacuous and citations.json is empty. I opened each existing statement dependency: def-pc-scheme supplies the base notion; def-trf-algebraic-space explicitly makes B a sheaf of sets on the big fppf site over S; lem-trf-space-fibre-products-etale-covers explicitly states that F times_H G is an algebraic space and the categorical fibre product. Only that first clause is needed here; no property of its etale-family clause is assumed.

For the Mathlib specialization I read CategoryTheory/Monoidal/Cartesian/Over.lean:30–38 and 53–81. Its sole extra typeclass hypothesis is HasPullbacks C. For C equal to fppf set-valued sheaves, Sites/Limits.lean:145–169 supplies finite limits and createsLimitsOfShape; no algebraicity, small-index colimit, flatness or local-finiteness assumption is introduced. The abbreviation chooses Over.mk (identity B) as terminal object and the sheaf pullback cone as product; tensorObj_left:59 and tensorObj_hom:62 confirm that object and its structure arrow. tensorUnit_left:65 and tensorUnit_hom:68 identify the unit exactly. lift_left:71–72, fst_left:75 and snd_left:78 identify the structural maps, so the match covers more than just existence of some cartesian structure. Algebraic-space closure is already the statement of the retained restriction dependency, rather than a theorem being extracted from a definition.

I tested the data on an empty base (every sheaf admitting a map to it is initial), the terminal base (ordinary sheaf products), one factor id_B (the product is the other factor), and equal factors (the relative diagonal is the universal lift). These all agree with the chosen pullback/unit formulas. There is no representability assumption on arbitrary slice objects F,H; algebraicity is required only for the restriction clause. The difference between Mathlib's explicit abbreviation and a globally registered instance is not a difference of mathematical data. No statement dispute or source error was found. Current leanfinder returned the ambient sheaf product structure, which I did not confuse with the relative product; Loogle and LeanSearch returned the exact slice abbreviation, confirmed by the logged grep and direct source reading.

## Unfinished

None in the stage-1 classification; server validation and push are performed after this report.
