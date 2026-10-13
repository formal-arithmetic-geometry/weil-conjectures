## What changed

Reworked the target proof to use a strictly smaller identity-representative intermediate theorem. The target now obtains the edge transformation from `exists_affinePushforwardCohomologyEdge_identity`, eliminates the supplied object equality, identifies the isomorphism with `Iso.refl`, and applies the identity equation. Added the intermediate module and DAG node. Included the existing coordinate source in the sandbox solely so local compilation can resolve its published-build gap.

## Proved and sorry left

The target declaration `AlgebraicGeometry.exists_affinePushforwardCohomologyEdge` is proved with no `sorry`. One strictly smaller hole remains in `AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity`, whose statement is the canonical-representative case. The existing helper `AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge` remains a dependency with its recorded `sorry`.

## No longer needed

The previous direct coordinate calculation, including its local preservation-instance setup and lemmas `hb`, `hnat`, and `hhom`, is no longer needed. No DAG dependencies beyond the identity intermediate, coordinate definitions, and sheaf-edge helper are used by the target proof.

## Where the brief, the DAG or earlier work was wrong

The earlier proof attempt had type mismatches in the tilde/Gamma counit calculation and final coordinate change. The published compiled build also lacks `AffinePushforwardComparisonCoordinates.olean`; the sandbox includes its unchanged repository source to make local compilation possible. This is a build artifact issue, not a target statement change.

## New nodes

Added `lem-pc-affine-pushforward-cohomology-edge-identity` for the strict identity-representative substatement, and retained the prior helper node `lem-pc-affine-derived-pushforward-sheaf-edge` used by it.

## Earlier second reading (a previous round; superseded)

The target proof was independently checked by compiling all sandbox modules. The identity intermediate is strictly smaller because it fixes the representative to `Q (T_A C)` and exposes its quasi-coherence proof; the target's equality hypothesis reduces every allowed `t` to this case. The remaining sorry is confined to that intermediate theorem.

## Second reading by Q4

1. Compared the delivered target module with the repository version. The declaration signature is unchanged byte for byte; only proof imports and proof text changed. Verdict: pass.
2. Compiled the target and the identity intermediate with `lcompile.py`; both compile without errors. The target has no `sorry`; the identity intermediate is the named split theorem documented above. No axioms, unsafe declarations, or hollow definitions were introduced. Verdict: pass.
3. Checked the identity intermediate against its DAG node and searched the library for duplicate declarations. Its statement is a strict canonical-representative restriction of the target and is needed by the target proof. Verdict: pass.
4. The proof uses the identity intermediate and retains the coordinate and sheaf-edge route; no shorter available declaration was found. The imported comparison-coordinate source is needed for the public statement, while the edge and identity imports are proof-only. Verdict: pass.
5. The target node proof and proof dependencies match the Lean proof, and the identity node records the added split theorem. The unit route remains the same. Verdict: pass.

Changed only the target proof and imports, added the identity intermediate module and node, and recorded the split theorem; no existing declaration signatures or definitions were changed.
