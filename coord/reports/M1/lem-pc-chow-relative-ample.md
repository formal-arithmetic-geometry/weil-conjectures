1. Files written:
- `dag/nodes/sec-picard-framework/lem-pc-chow-relative-ample.json`: item, statement, four proof steps, no new nodes, no Mathlib leaf.
- `citations.json`: verbatim statement citations for every node used by every step.

2. Attachments: none.

3. WANTED: literature/stacks-project/coherent.tex, Proposition 30.19.1 (Tag 02O5) and Remark 30.18.2 (Tag 0200), because the source checkout is not materialized in this repository; the item node records the exact source places and the imported DAG supplies the statements used.

4. The imported item was unsplit even though its parent proof already identified the needed route. I retained its statement and added the missing proof. No statement error or blueprint error was found. No new node was created: `lem-weil-pbc-chow-noetherian` already supplies the Chow immersion setting, `lem-weil-pbc-projective-ample-invertible` already supplies affine-base ampleness, and the permanence and immersion criteria already exist as nodes.

## Review by M1
I read the item and its parent `lem-pc-coherent-hi`, including the parent Chow step, and checked the source references recorded in the item against the imported Stacks labels 02O5/0200 and the existing DAG statements. Step 1 uses the proper-composition/base-change permanence statement for properness and projective-space properness, the proper-over-separated statement for `j` being proper, and the immersion-with-closed-image statement for closedness; each cited node explicitly states the property used. Step 2 uses the permanence statement's closed-immersion base-change clause, the projective-morphism definition, and the projective-space definition to identify `(j, pi)` and conclude that `pi` is projective; the pullback identification is the canonical base-change compatibility named in the source. Steps 3 and 4 apply the existing `lem-weil-pbc-projective-ample-invertible` statement after restricting to affine opens of `S` and `Z`; its hypotheses are met because the restricted maps are closed immersions into the corresponding relative projective spaces, and its conclusion is exactly ampleness of the pulled-back `O(1)`. I checked the small edge cases conceptually: empty affine opens are vacuous, `m=0` is allowed, and identity base changes preserve the conclusions. I corrected the initial proof draft by adding `lem-weil-pbc-proper-fp-permanence` for both composition and closed-immersion base change and by regenerating all citation quotes verbatim from the node statements.

The projective ampleness node is an off-unit generic tool use, declared in `split_report.tool_uses`: it is the only existing statement that supplies the affine-base `O(1)` ampleness needed by steps 3 and 4, and the coherence unit has no route-local replacement.

5. What remains unfinished: no proof or node remains unsplit below this item; the second worker should independently reread the four steps and deliver the accepted dry-run packet.

## Second reading by M1
I checked the item against the Chow paragraph of Proposition 30.19.1 (Tag 02O5) and Remark 30.18.2 (Tag 0200), hypothesis by hypothesis. No new node is present; every auxiliary node cited by the four steps was opened and its statement checked. Step 1 uses proper composition, proper-over-separated, closed image for an immersion, the projective definition, and projective-space properness. Step 2 now explicitly uses properness implying separatedness, the graph as the pullback of the diagonal, and closed-immersion base change and composition; this supplies the missing justification for `(j, pi)`. Steps 3 and 4 apply the affine-base projective ampleness node after restriction to affine opens of S and Z. Empty schemes and empty affine opens are vacuous; m=0 and identity maps preserve the conclusions.

Changed step 2 to add the graph argument and its properness citation; no nodes were added or removed. The existing generic projective-ampleness node remains the declared tool use.
