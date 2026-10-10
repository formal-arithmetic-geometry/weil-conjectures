# lem-sc-p1-finite-homogeneous-generators

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-p1-finite-homogeneous-generators.json`: item split; no new nodes and no new Mathlib leaves.
- `citations.json`: the verbatim shift-definition citation for proof step 2.

## Attachments

None. A search of `WeilConjectures/` for the item id, its blueprint tag, and homogeneous generators found no declaration stating this item. `ProjectiveSpace/Duality.lean` lines 77-94 describes a graded resolution in a docstring, but its theorem concerns sheaves and has `sorry`.

## Wanted

WANTED: `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-duality/lem-sc-p1-graded-resolution.md`, proof of the initial graded free module, for `lem-sc-p1-finite-homogeneous-generators`. The blueprint literature tree is absent in this checkout. The imported `lem-sc-p1-graded-resolution` node preserves the relevant proof sentence and source note. The argument below is therefore marked agent-written.

## Node and source findings

The item's statement is true with the total-degree grading already written in it. Its imported proof was empty. I kept the statement and both existing statement dependencies, and expanded the free-module construction into three steps. The citation to `def-sc-p1-standard` supplies the projective-line convention, while the statement itself specifies the polynomial grading. The shift needed for the free module is defined by `def-weil-pbc-proj-twisting-sheaf` (2). No Stacks tag asserts a separate non-elementary fact in these steps.

I searched the whole DAG by homogeneous generators, graded module, and the source phrase, then searched imported blueprint nodes with `blueprint_refs.py search homogeneous generators` and `search graded module`. Neither has a node stating this assertion. The Mathlib searches already recorded in the item found no exact declaration; a fresh source search found `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous` for algebra generators, not generators of a graded module. No new node was warranted.

## Review by G1

I read the item's statement, the imported `lem-sc-p1-graded-resolution` statement and proof, the unit and chapter records, the two cited definition nodes, and the Lean docstring in `ProjectiveSpace/Duality.lean`. The missing blueprint file is named above. The source note and ancestor proof call for a finite graded free presentation, and this item proves precisely its initial surjection; it does not absorb the later syzygy argument. There are no new node statements to compare with sources.

Step 1 uses only finite generation and the direct-sum meaning of a graded module: each ordinary generator has finitely many homogeneous components, and all components together generate. Step 2 cites the exact sentence in `def-weil-pbc-proj-twisting-sheaf` (2) defining `M(d)_n=M_{d+n}`. Substituting `d=-d_j` shows the basis vector has degree `d_j`, and the displayed multiplication map preserves degree because `S_{n-d_j} M_{d_j}` lies in `M_n`. Step 3 uses the span equality from step 1 to prove surjectivity. The steps rely on no unmentioned existence or exactness theorem.

For the hypotheses, the direct-sum grading guarantees finite support in step 1; finite generation supplies a finite initial set; the graded module action supplies the degree calculation in step 2. The statement is valid when `M=0` (empty generators and zero free module), `M=S` (generator 1 in degree 0), and `M=S(-1)` (generator 1 in degree 1); these also check the sign of the shift. I found no false clause or missing hypothesis. I corrected the empty imported proof, and kept its source gap explicit instead of attributing my expanded argument to a document I could not open. I checked B1-B10, C1-C8, D1-D5, and E1-E7 against the item and the available source records: no new node is introduced, every cited statement says the fact used, and the steps prove the item directly without a circular or relabelled dependency.

## Unfinished

Nothing in the split. The blueprint source file remains unavailable on this machine and is reported under Wanted.
