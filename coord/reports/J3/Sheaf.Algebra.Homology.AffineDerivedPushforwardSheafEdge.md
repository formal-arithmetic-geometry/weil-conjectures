## What changed
Replaced the target theorem's proof with a real composition of two strictly smaller named intermediate theorems. Added `AffineDerivedPushforwardSheafEdgeExistence` and `AffineDerivedPushforwardSheafEdgeCompatibility`, each imported privately by the target module. Both intermediate proofs remain explicit named `sorry` holes with source documentation.

## Proved and sorry left
The target declaration `AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge` is proved by extracting an edge from the existence theorem and applying the compatibility theorem. Remaining holes are `exists_affineDerivedPushforwardSheafEdge_existence` (node `lem-pc-affine-derived-pushforward-sheaf-edge-existence`) and `affineDerivedPushforwardSheafEdge_compatibility` (node `lem-pc-affine-derived-pushforward-sheaf-edge-compatibility`).

## No longer needed
None; the original public imports remain needed for the target signature, while the proof-only imports are the two new intermediate modules.

## Where the brief, the DAG or earlier work was wrong
The DAG presented a long construction without separately stated Lean interfaces for existence and normalization. The proof therefore splits those two mathematically distinct steps into named intermediate nodes.

## New nodes
`lem-pc-affine-derived-pushforward-sheaf-edge-existence` and `lem-pc-affine-derived-pushforward-sheaf-edge-compatibility` are added under `sec-picard-framework`.

## Second reading by J3

1. I compared the delivered target module with the repository version. The target declaration and all existing signatures are unchanged; only its proof imports two private helper modules. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile successfully. The only remaining `sorry`s are the two named split-off helper theorems, and no forbidden declaration or hollow definition was introduced. Verdict: pass.
3. I checked both split-off statements against their uses and source descriptions. The existence statement is exactly the first conjunct needed by the target, and the compatibility statement is exactly the universal second conjunct; neither duplicates the full target. Their DAG nodes and docstrings identify the cited Stacks sources. Verdict: pass.
4. I checked the proof route and imports. The target extracts the edge from the existence helper and applies the compatibility helper; both helpers are imported privately, while the target's public imports remain unchanged. The unit record is unchanged and the route still realizes the target statement. Verdict: pass.
5. I searched the local library and recorded the Mathlib/library search results in the node metadata. No existing declaration states either split-off result, and no shorter proved route was found. Verdict: pass.

Changed in this second reading: replaced the extraneous `True` witness conjunct in the existence helper with `Nonempty` and adjusted the target proof and node metadata accordingly; added this review record.
