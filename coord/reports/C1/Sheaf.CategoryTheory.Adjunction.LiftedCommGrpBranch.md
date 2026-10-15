## What changed

Withdrew the duplicate module `lean/Sheaf/CategoryTheory/Adjunction/LiftedCommGrpBranch.lean`.
The theorem only repackaged Mathlib's `Functor.mapCommGrp` and
`Adjunction.mapCommGrp`. Re-pointed the group branch in
`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects` to those declarations directly,
including the operation, unit, counit, hom-equivalence, and existence formulas.
Change record: `coord/changes/liftedCommGrpBranch.md`.
The changed caller node now cites the existing abelian-group Mathlib leaf directly;
the retired wrapper node's Lean attachment is removed with `lean: null`.

## Proved and sorry left

This is a duplicate repair, so no target theorem is newly proved. The withdrawn module had
no remaining `sorry`; its duplicate declaration is removed.
Holes closed: none (0 of 0). Holes added or split off: none. The adapted caller compiles
with the direct Mathlib construction and introduces no `sorry`.

## No longer needed

Removed the duplicate declaration `CategoryTheory.Adjunction.liftedCommGrpBranch` and its
module, its public import `Mathlib.CategoryTheory.Monoidal.CommGrp_`, and the caller's
proof import `Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch`.
Node `lem-weil-pbc-lifted-comm-group-branch` is no longer a dependency of the caller.
No Mathlib declarations are pruned: the caller now uses `Functor.mapCommGrp` and
`Adjunction.mapCommGrp` directly.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1424 correctly identified `liftedCommGrpBranch` as a duplicate wrapper.
The wrapper's existential statement and proof were exactly the Mathlib construction plus
identity comparison formulas, so retaining a separate declaration added no mathematical
content. The caller was re-pointed without changing its public statement.

The unit `sk-def-exchange` realizes neither this auxiliary wrapper nor the adapted
caller as a unit statement or step. The unit route is unchanged. The documentation-only
reference in `SitePullbackAbelianUnderlying` is stale; that module already uses
`Adjunction.mapCommGrp` directly in its proof and is unchanged in this delivery.

## Forced adaptations

`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects` is unclaimed in the repository
claim snapshot. The original caller was compiled against an empty withdrawn module using
`lcompile.py --all` on the counterfactual scratch set. It fails at line 148 with:

```text
error(lean.unknownIdentifier): Unknown identifier `liftedCommGrpBranch`
```

The adaptation removes its proof import (old line 11) and replaces its final call
(old line 148) with the direct Mathlib group construction and the required formulas.
The unchanged ring branch still calls `liftedCommRingBranch`. All existing public
signatures and visibility in the caller remain identical; the adapted file compiles.


## Second reading by C1

1. **Interfaces: PASS.** Compared every delivered Lean file and both nodes with the
   repository versions. The sole surviving declaration,
   `CategoryTheory.Adjunction.liftsGroupRingObjects`, has a byte-for-byte identical
   signature and unchanged public visibility and imports. The removed declaration is
   explicitly authorized by upstream review #1424 and recorded in
   `coord/changes/liftedCommGrpBranch.md`. Only the caller uses it in code.
2. **Proof and axioms: PASS.** Independently compiled the adapted caller with
   `lcompile.py` (no errors or warnings). A scratch copy with
   `#print axioms CategoryTheory.Adjunction.liftsGroupRingObjects` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`. No delivered declaration contains
   `sorry` or prohibited constructs; no data or definitions are added. The original
   caller against an empty withdrawn module independently fails at line 148 with
   unknown identifier `liftedCommGrpBranch`, confirming the adaptation is forced.
3. **Split statements: PASS (none).** No new statements, nodes, or holes are added.
   Read Mathlib's `Functor.mapCommGrp`, `Adjunction.mapCommGrp`, and the Cartesian
   comparison formulas. These supply the direct construction; the existence iff is
   proved by applying the lifted hom-equivalence and its inverse, cancelling with
   injectivity of the original equivalence. It does not assume an arbitrary witness.
4. **Route, imports, pruning: PASS.** The removed wrapper's proof is now directly in
   its sole caller, using the existing Mathlib constructions. Every retained import
   is used. All three old caller dependencies are accounted for: right-adjoint limit
   preservation and the ring branch remain, and the group wrapper is replaced by the
   existing abelian-group Mathlib leaf. The removed wrapper node had only that leaf
   as its proof dependency, which remains used. `sk-def-exchange.realized` names
   neither auxiliary node as its statement or a step; the unit route is unchanged.
5. **DAG and records: PASS.** Both node diffs change only `proof`, `proof_deps`,
   `proof_origin`, and (for the retired wrapper) `lean: null`. The updated caller
   dependencies match the proof; the retired attachment is removed. No target,
   definition, mathematical statement, or unit record changes.

Second-reading changes: corrected the change record's stale downstream count from
68 to 69 and expanded its Users table to include every current downstream module
and its claim holder. Made the zero holes closed/added count explicit above. No
Lean or node repair was needed.
