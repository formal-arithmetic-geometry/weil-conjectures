1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-genus-invariant.json`: item split; no new nodes.
- `citations.json`: three verbatim statement quotes for step 1.

2. Attachments

None.

3. WANTED

None.

4. Issues found

The imported proof was mathematically on the right route but did not identify the exact clauses used from the cited statements. I made the step explicit: the definition gives both genus values as dimensions of `H^1`, the existing flat coherent base-change lemma gives equality of those dimensions for an algebraically closed extension, and the Jacobian theorem explicitly supplies the base-change isomorphism. I found no existing node or Lean declaration stating this target exactly, and created no duplicate node. The item remains under its original proper, smooth, connected, algebraically closed hypotheses.

## Review by C1

I read the target source `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-ext-invariance/lem-sc-genus-invariant.md` and checked the imported statement against the definitions in `def-sc-curves` and `def-sc-genus`. For step 1, `def-sc-genus` says that genus is `dim H^1`; `lem-sc-flat-base-change-coherent` says that these dimensions agree after an algebraically closed field extension for a proper scheme and the structure sheaf; and `thm-sc-jacobian-representability` says that the Jacobian is compatible with extensions of separably closed fields. The target hypotheses provide the proper curve and algebraically closed extension required by the base-change statement, and algebraically closed fields are separably closed for the Jacobian clause. I recorded exact quotes in `citations.json` and verified that every cited node's statement contains the quoted fact. I also ran the required LeanFinder, Loogle, and Mathlib grep searches for the item; they returned no matching Mathlib declaration. No new statement required small-case repair, and no source or DAG node was modified outside this item.

5. Unfinished

Nothing.

## Second reading by C1

- Step 1 checked against the blueprint proof paragraph beginning “By [def-sc-genus]”, [def-sc-genus], [lem-sc-flat-base-change-coherent], and [thm-sc-jacobian-representability]; verdict: correct hypotheses and conclusions, with each cited fact supported by the verbatim quotes in `citations.json`.
- New nodes: none; the step uses existing statement nodes, so no new-node statements or Mathlib leaves required review.
- Small cases checked: $k'=k$ gives equality by reflexivity; $C=\mathbf P^1_k$ gives genus $0$ on both sides; the proper smooth connected hypotheses exclude the empty scheme and zero object.
- Blueprint search checked `lem-sc-genus-invariant` and its nearest ancestor; verdict: no distinct blueprint node states this fact, and provenance now records the item’s own proof paragraph.
- Mathlib searches checked the recorded LeanFinder, Loogle, and source grep results; verdict: no matching Mathlib declaration.
- Changed the blueprint `from` provenance from `null` to the item’s proof paragraph so the split records the exact clause it realizes.
