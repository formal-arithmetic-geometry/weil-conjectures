## What changed

Proved `AlgebraicGeometry.relativeMV_composite_baseChange_target_transpose` in
`Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangeTargetTranspose` by the recorded
adjunction argument. Its public statement, visibility, and imports are unchanged.

Five proved private helpers organize the calculation: `imageComp_counit` gives the
composition-mate counit equation; `restriction_counit` cancels the transpose defining
relative restriction; `restriction_transpose` moves an arbitrary incoming arrow through
that equation; `relativeMVOpenLift_fst` pins the first-projection equation; and
`comparison_witness_eq` identifies the pinned comparison with the original equality
transport by congruence and proof irrelevance. The base-change arrow is not expanded.
The original unused local let bindings are retained; the unused-variable linter is
scoped off for the existing public declaration only.

The node's proof records the comparison-witness normalization. Its dependencies and
mathematical route remain the same. No definitions or public interfaces changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.relativeMV_composite_baseChange_target_transpose`
(node `new-relative-mv-composite-base-change-target-transpose`).
All five private helpers are also proved. The delivered module has no `sorry`.
Holes closed: 1. Holes added: 0. No intermediate statements were split off.

## No longer needed

None. No imports, nodes, or modules were pruned. The only imported project module is
`Sheaf.AlgebraicGeometry.RelativeMVMaps`, which supplies the definitions used in the
statement and calculation.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt contained an unfinished `simp` proof and a report saying
that the original hole remained. Both have been replaced by the complete proof.

The kernel timeouts had a specific cause: inferring the source of `congrArg` directly
from `pullback.lift_fst` repeatedly made Lean reduce the chosen pullback construction
when comparing the composition with `relativeMVOpenLift`. A named projection theorem
pins that source. The private comparison equality transports the proof to this witness
without changing the public statement. The recorded adjunction plan needs no new
mathematical assumptions or unfinished lemmas.

Validation: the delivered module compiled without warnings in 13.9 seconds. Its
unchanged direct user, `Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangeCounit`,
compiled against the delivery in 5.0 seconds. No adaptation was required or delivered.
The delivery dry run checks the declarations and axioms, report, and DAG record.

## Second reading by N3

1. **Interfaces unchanged — pass.** Compared the only delivered Lean module with the
   repository using `diff -u`, and separately checked the complete existing theorem
   signature byte for byte. Its signature, visibility, public import and docstring
   are unchanged. No definition or change record is added. The five new declarations
   are private proved helpers, used only by this proof.
2. **Kernel proof — pass.** Independently compiled the delivered module through
   `lcompile.py` without errors or warnings (8.5 seconds). A scratch copy containing
   `#print axioms` for the public theorem and all five helpers compiled (9.2 seconds):
   every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
   No `sorryAx`, remaining `sorry`, forbidden declaration, or data construction is
   introduced. The comparison-witness normalization uses proof irrelevance only.
3. **Split statements and edge cases — pass.** There are no split-off statements or
   new holes. The counit calculation holds for arbitrary factorizations and incoming
   arrows; hence equal opens, empty opens, identity and zero arrows require no extra
   assumptions. The projection helper is precisely `pullback.lift_fst` and the
   comparison helper is congruence on equality proofs. The other helpers follow mate
   counit compatibility, naturality, and inverse Hom-equivalence cancellation.
4. **Shortest route, imports and unit — pass.** Re-searched the source library and
   Mathlib for restriction transposes and right-adjoint uniqueness counit equations,
   and checked the Mathlib uniqueness/Hom-equivalence lemmas. These are the building
   blocks already used; no public declaration provides this pinned restriction
   formula directly. `RelativeMVRestrictionSourceCounit` has identical private counit
   helpers, which are not public reusable declarations; its public source-path
   formula is a different calculation. Importing it would not shorten this proof.
   The sole import `RelativeMVMaps` supplies statement definitions and is correctly
   public. The old and new `proof_deps` are both exactly `def-pc-relative-mv-maps`;
   nothing is pruned. The unit `sk-thm-picard-semicon` and its `realized` entries are
   unchanged; this node retains the original local adjunction route.
5. **DAG agrees — pass.** The only changed node fields are `proof` and `proof_origin`.
   The added step records the projection-witness normalization used by the Lean
   proof. The remaining steps describe the composite counit, naturality and transpose
   cancellation, with their dependency union unchanged. No new nodes are needed.

Second reading changed only this report: added the independent review, signature
comparison, search findings and kernel/axiom verification. The Lean proof and DAG
were correct and were retained.
