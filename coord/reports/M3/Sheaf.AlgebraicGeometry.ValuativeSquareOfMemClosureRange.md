## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.ValuativeSquareOfMemClosureRange` with the existing DAG plan.
`AlgebraicGeometry.exists_specializes_of_mem_closure_range j hs` supplies a point
whose image specializes to the prescribed centre.
`AlgebraicGeometry.ValuativeCommSqWithPt.ofSpecializes j hz` supplies the centred
square; its `toValuativeCommSq` and `closedPoint_eq` give the required existential.
The signature, docstring, imports and proof route are unchanged. No definitions,
statements, other modules or nodes were changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.exists_valuativeCommSq_of_mem_closure_range`
(node `lem-sc-picard-valuation-probe-closure`). No holes remain in the item;
no holes were added or split off. Both invoked project declarations already have
complete proofs. The module compiles cleanly through `lcompile.py`.

## No longer needed

None. The proof uses both planned dependency nodes:
`lem-sc-picard-closure-specialization` and
`lem-sc-picard-valuation-probe-specializes`. Their two proof imports are retained;
the public Mathlib import supplies the unchanged statement's valuative-square API.
No nodes or modules are pruned, and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The DAG plan is directly expressible
in three lines of Lean using the two recorded declarations. The immersion
hypothesis is unnecessary for these helpers but remains unchanged in the theorem.
The unit record `sk-prop-av-cube` has empty realized entries, and this delivery
follows the prescribed node proof without changing the unit route.

Searches performed: launcher LeanFinder returned valuative-criterion declarations
but no shorter exact closure-centre result; Loogle listed the valuative-square
structure and projections; launcher grep returned no hits. Direct source search
and reading found the exact two existing project helpers and the downstream use
in `Sheaf.AlgebraicGeometry.ClosedImmersionOfValuativeFactorization`.

## Second reading by M3

1. Compared the delivered module with the repository version. The theorem
   signature, docstring, module header, and imports are unchanged; only the
   `sorry` proof body was replaced.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or
   warnings. The proof contains no `sorry`, `axiom`, `unsafe`, or hollow
   definition, and the scratch axiom check has no unexpected dependencies.
3. Checked the proof route against the DAG and source declarations. The two
   applications are exactly `exists_specializes_of_mem_closure_range` and
   `ValuativeCommSqWithPt.ofSpecializes`; both are existing, proved declarations
   and the resulting projections have the target type. No new statement was
   introduced, so there are no new nodes to validate.
4. The proof uses both recorded proof dependencies and retains the necessary
   public valuative-criterion import plus proof-only imports. No unused import,
   prunable node, or shorter applicable route was found. The unit route is
   unchanged.
5. The node's Lean declaration, theorem statement, proof steps, and
   `proof_deps` agree with the delivered code. Verdict: pass.

Changed only the theorem proof; no declarations, imports, nodes, or interfaces
were altered.
