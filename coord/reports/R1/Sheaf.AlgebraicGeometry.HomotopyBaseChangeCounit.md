## What changed

Filled `AlgebraicGeometry.moduleHomotopyBaseChange_counit` in
`Sheaf.AlgebraicGeometry.HomotopyBaseChangeCounit` without changing its signature,
visibility, existing docstring, or imports. Added only proved private helpers:
`map_counit`, `equality_mate`, `ordinarySquare_mate`, `ordinary_counit`, and
`homotopySquare_eq`, together
with private abbreviations/constructions for the adjunction and ordinary square.
The ordinary identity follows from Mathlib's inverse and iterated mate identities;
a generic additive-functor calculation descends it degreewise through the homotopy
quotient. Updated the existing node's proof route and dependency list to match.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.moduleHomotopyBaseChange_counit`
(node `lem-pc-homotopy-base-change-counit`). Added zero holes. Every private helper
is fully proved, and there is no `sorry` in any delivered file. The proof uses the
existing tensor-pullback adjunction and base-change naturality declarations.

## No longer needed

No imports, nodes, or modules were removed: the three original public imports are
needed by the unchanged statement and its definitions. No new proof import is
needed. The theorem `homotopyPullbackSquare_localization` is not used; its module
supplies the real definition `moduleHomotopyPullbackSquare` used in the statement.
The expanded unit/naturality/triangle calculation from the original plan is
replaced by the existing Mathlib mate identities.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The first compile was blocked because
the published local build lacked `HomotopyPullbackSquareLocalization.olean`; the
artifact appeared during this session, resolving the blocker without modifying
or compiling any dependency. Direct simplification with concrete scheme functors
unfolded tensor-pullback data too aggressively. Proving the quotient calculation
for generic additive functors kept the same argument within the compile limit.
The final application also needed an explicit proved equality for the homotopy
square: rewriting with `homotopySquare_eq` avoids a costly whole-statement kernel
conversion. The actual module compiled cleanly with `lcompile.py` in 17.8 seconds.

## Second reading by R1

1. **Interface and accidental changes.** Compared the delivered module with the repository version. The theorem signature, visibility, docstring, imports, and all existing declarations are unchanged; only the proof and private helpers were added. The node diff records the corresponding proof route and dependencies.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; compilation succeeds. Searched the delivered Lean file for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`; none occur. The sole previous hole, `AlgebraicGeometry.moduleHomotopyBaseChange_counit`, is closed and no new holes were added. The helpers use ordinary adjunction mate identities and degreewise quotient descent, with no arbitrary witness data.

3. **Statements and new declarations.** No new public statement was introduced. The private helpers are internal proof reductions, and the existing theorem statement is unchanged. The node's proof text now matches the actual ordinary-mate and homotopy-quotient argument; its dependencies include exactly the declarations imported and used by that proof.

4. **Shortest route and pruning.** Checked the proof against the imported declarations and Mathlib mate identities. The route uses the generic `mapHomotopyCategory` counit calculation and the ordinary counit mate, avoiding the longer expanded triangle calculation. All three original public imports remain necessary for the theorem's statement or definitions, and no unused proof import was introduced. The localization theorem is used through its defining `moduleHomotopyPullbackSquare`.

5. **DAG and unit consistency.** The node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof. The unit route is preserved: `moduleHomotopyPullbackSquare` remains the realized localization step, followed by the ordinary base-change mate and quotient calculation. No statement or definition was changed.

I changed only the proof of `moduleHomotopyBaseChange_counit`, added private helpers needed for the mate calculation, and updated the existing node's proof route/dependencies. No imports, modules, or holes were added or removed beyond closing the target hole.
