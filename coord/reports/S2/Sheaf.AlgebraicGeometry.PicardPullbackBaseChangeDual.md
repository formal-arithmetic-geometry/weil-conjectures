## What changed

Proved `AlgebraicGeometry.Scheme.picard_pullback_base_change_dual` without changing
its signature. Added proof-only imports of
`Sheaf.AlgebraicGeometry.PicardPullbackBaseChangePrimal` and
`Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree`.

The fully proved private helper `tensorPullback_dual_iso` identifies tensor
pullback of a finite locally free dual with the dual of tensor pullback. It uses
uniqueness of left adjoints to transfer the existing ordinary-pullback comparison.
Dualizing the given isomorphism and composing the two comparisons supplies the
hypothesis of the primal theorem applied to the dual bundles. Both dual bundles
are finite locally free by the existing proved `Modules.IsFiniteLocallyFree.dual`.
Updated the item's DAG proof, proof dependencies and proof origin accordingly.
The public-import removal has change record
`coord/changes/picard-pullback-base-change-dual-imports.md`. Its direct importer
and the only downstream user of the finite-unit theorem already import the
finite-unit module themselves; no adaptations are needed.

Read Stacks Tags [0BDP](https://stacks.math.columbia.edu/tag/0BDP) (the projection
formula and its dual clause) and [0FNV](https://stacks.math.columbia.edu/tag/0FNV)
(finite locally free duality). The unit `sk-prop-av-cube` has no realized nodes
assigned to its statement or steps; this change preserves its route and only
reuses an existing tool below the unit level. The comparison from the tangent
unit is used solely as a general pullback-duality tool.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.picard_pullback_base_change_dual`
(node `lem-sc-picard-pullback-base-change-dual`). No sorry remains in the
item's module, and no holes or modules were added. The private helper is proved.

This is a proof from existing named declarations, rather than a claim that the
entire transitive dependency closure is sorry-free. In particular the existing
`AlgebraicGeometry.Scheme.picard_pullback_base_change_primal` still contains
sorry in its own module. The pullback-duality comparison is already proved,
and the second reader's local axiom probe confirms that the private helper
depends only on `propext`, `Classical.choice` and `Quot.sound`. The main
theorem additionally depends on `sorryAx` through the existing primal theorem.

The final file compiled cleanly via lcompile.py. The argument applies equally
to rank zero and empty schemes: all comparisons are functorial isomorphisms,
and the primal theorem accepts those cases unchanged. No data definition was
added and no arbitrary witness is selected in a definition.

## No longer needed

Removed the direct import
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit`. Its node
`lem-sc-finite-locally-free-tensor-unit` and the open-restriction proof node
`lem-weil-pbc-module-base-change-map-open-restriction` are no longer direct
proof dependencies of this item: the proof reuses the primal result instead
of repeating the local-frame calculation. The open-restriction module stays
publicly imported because it defines `Modules.moduleBaseChangeMap` in the
statement. FiniteLocallyFreeTensorUnit remains reachable through the primal
module, so no complete module in the targets' import closure is claimed pruned.
All remaining imports supply the statement or actual proof declarations.

## Where the brief, the DAG or earlier work was wrong

The original proof plan asked to repeat the local-frame argument for the dual.
That repetition is unnecessary: the primal theorem specializes to the dual
bundles after transferring the already available pullback-duality isomorphism
from ordinary pullback to tensor pullback. No statement was found false and
no declaration interface or target signature was changed. The redundant public
import removal is documented in the change record named above.

Searches run through msearch.py: LeanFinder for pullback of finite locally free
duals returned free-pullback comparisons and the ordinary adjunction, with no
exact duality match; Loogle for dual and pullback returned zero hits; the logged
grep for the comparison's name returned zero hits in its search corpus. Direct
repository rg found the existing PullbackDualFiniteLocallyFree module and its
DAG node. No search was represented as an exact match without inspecting its
source signature.

## Second reading by S2

1. **Interface — pass.** Compared the sole delivered Lean module with the
   repository using `diff -u` and extracted the original theorem signature:
   it is byte for byte unchanged. The only visible import removal is recorded
   in `coord/changes/picard-pullback-base-change-dual-imports.md`. Verified the
   sole direct importer imports the finite-unit module independently and
   privately imports this module. Re-ran `tools/downstream.py --uses`: the
   only affected downstream user of the finite-unit theorem is Evaluation,
   which imports the finite-unit module itself. No definitions are changed.
2. **Proof — pass.** Compiled the module cleanly with `lcompile.py` and compiled
   a scratch copy printing both declarations' axioms. The private comparison
   uses only `propext`, `Classical.choice`, `Quot.sound`; the public theorem
   also uses `sorryAx` from the existing open primal theorem. No local `sorry`,
   forbidden declaration, hollow definition or data construction was added.
   Checked every isomorphism direction: c goes from tensor to ordinary
   pullback; mapping c.op goes from the ordinary dual to the tensor dual;
   mapping i.op is inverted to go from dual(q*E) to dual(p*N).
3. **Split statements — pass (none).** No new open statements or nodes.
   The proved private helper is only the pullback-duality comparison, strictly
   simpler than base change. Checked dual local frames at rank zero, empty
   schemes and locally varying ranks. Inspected the existing dual-pullback,
   dual finite-local-freeness and exact-pairing declarations. An additional
   conceptual rg/msearch search found the existing comparison, with no shorter
   tensor-pullback duality theorem. No duplicate public theorem was introduced.
4. **Route and pruning — pass.** Applying primal base change to the duals is
   the direct reduction; the helper supplies exactly its isomorphism hypothesis.
   Proof-only imports are private. Remaining public imports provide statement
   APIs. Both removed old proof dependencies are listed under No longer needed.
   The finite-unit module is still transitively reachable, so the number of
   completely pruned modules is zero. Read sk-prop-av-cube.json: its realized
   statement and step lists are empty, and no unit route was bypassed.
5. **DAG — pass.** The node's three proof steps, their uses and proof_deps agree
   with the adjunction comparison, pullback-duality theorem and primal theorem
   used by Lean. Its statement, stmt_deps and lean.statement are unchanged;
   proof_origin documents the reduction. Checked the source's dual clause in
   [Stacks 0BDP](https://stacks.math.columbia.edu/tag/0BDP) and the finite-free
   duality calculation in [Stacks 0FNV](https://stacks.math.columbia.edu/tag/0FNV).

**Second-reading changes:** no Lean or DAG repairs were necessary. Clarified
in the report that the compiled private helper has only standard axioms, while
closing the item's one hole still relies on the existing open primal theorem.
Added this independent review. Holes closed: one; holes added: zero.
