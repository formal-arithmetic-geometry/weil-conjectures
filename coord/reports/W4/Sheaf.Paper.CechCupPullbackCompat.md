## What changed

Added the proof-only import `Sheaf.Paper.ModuleCupPullbackResolutionMaps` and proved
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality` from its existing
resolution-map theorem. A proved private helper, `additive_map_exists_cycle`, transports
concrete kernel cycles through additive cochain maps between complexes over different
scalar rings. The proof represents the two input classes by cycles, forms their paired
cycle using Leibniz, transports all three cycles, and combines the three class equations
with the pairing equation and the two cup-product characterizations.

Local compilation succeeded in 33.4 seconds; the only style warning was fixed by
explaining the local heartbeat allowance.

All existing public signatures, definitions, and visibility are unchanged. The theorem
uses the same local heartbeat allowance as the module's other substantial transport
proofs. Updated the existing DAG node's proof and proof dependencies to record this route.
The unit `sk-prop-av-cube` has empty realized lists; its route is unchanged.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`
(node `lem-sc-picard-cech-cup-pullback-compat`).
No holes were added or split off. No `sorry` remains in the item's module.
The proof uses the existing `moduleCup_pullback_resolution_maps` theorem; its downstream
resolution construction remains a separate existing item, rather than a new hole here.

## No longer needed

None. Every original direct import is used by existing statements or proofs, and the
new proof-only import supplies the simultaneous pullback resolution maps. No module or
node is claimed pruned. In particular no auxiliary Cech cover, affine-comparison
isomorphism, or new resolution statement is needed for this last proof.

## Where the brief, the DAG or earlier work was wrong

The node's earlier progress notes said pullback naturality remained unproved. The current
library already supplies `moduleCup_pullback_resolution_maps`; this closes the remaining
step directly. No mathematical statement was found wrong. Semantic search returned only
general pullback APIs, and Loogle confirmed the cochain-map commutation API; local source
search found the needed project theorem. The local Stacks source is absent, so the existing
source descriptions were checked against the Stacks Project pages for Tags 0FKU and 0FKV.

## Second reading by W4

1. Compared the sole delivered Lean module against the repository with `diff` and
   the declaration comparison in `stage3_delivery.py`. Every existing declaration's
   signature, visibility, definition body, and docstring is unchanged. The additions
   are the proof-only import, the proved private `additive_map_exists_cycle`, a local
   heartbeat allowance, and the proof of `moduleCup_pullback_naturality`. Verdict: pass;
   no statement change or change record is needed.
2. Independently compiled the module cleanly in 34.7 seconds. A scratch copy with
   `#print axioms` for all seven public theorems compiled cleanly in 36.3 seconds.
   Four use only `propext`, `Classical.choice`, and `Quot.sound`; the main compatibility,
   pullback naturality, and refinement composition also use `sorryAx` from existing
   imported open results. In particular the new pullback proof remains conditional on
   the existing resolution construction, rather than an axiom-free closure of that
   dependency. No `sorry` or forbidden declaration occurs in the delivered module;
   no data-bearing definition was added or changed. Verdict: pass for stage 3.
3. No statements were split off and no holes were added. Read the private helper:
   its witness is explicitly the image cochain, and cochain-map commutation, the
   source cycle equation, and preservation of zero prove kernel membership. This
   works in degree zero, for the zero map and zero complexes, and for different
   scalar rings. The helper chooses no data from an unproved existence theorem.
   The resolution witnesses are eliminated only within a theorem proof. Verdict: pass.
4. Read the proof from the top down and the statement and proof of
   `moduleCup_pullback_resolution_maps`. Its three class equations have exactly the
   orientation and tensor coefficient comparison required here; its strict pairing
   equation supplies the last equality after transport. Source search for additive
   cycle transport and pullback cup naturality found no shorter public theorem:
   `ModuleCupResolutionFMap` has private additive-cycle machinery, while the existing
   same-ring helper cannot transport between the two section rings. The direct
   kernel construction is appropriate. All original imports serve unchanged
   statements or proofs; the new import is plain `import`. No old proof dependency
   is dropped, so `No longer needed: None` is complete. Inspected
   `dag/units/sk-prop-av-cube.json`: its realized statement and step lists are empty
   and this delivery does not alter or bypass a realized unit step. Verdict: pass.
5. Compared the sole delivered node with the repository. Only `proof`, `proof_deps`,
   and `proof_origin` differ. The new final step describes cycle surjectivity,
   Leibniz, additive kernel transport, the three class rewrites, and the strict
   pairing equality exactly as Lean implements them. Its new dependency is the
   existing `lem-sc-module-cup-pullback-resolution-maps`; the complete `proof_deps`
   equals the union of the steps' `uses`. No new nodes are needed. Verdict: pass.

Second reading changed only this report, adding the independent checks and the
explicit imported-axiom qualification. No Lean or DAG repair was necessary. One
existing hole is closed, none are added, and none are split off; this is a proof
from existing dependencies, not a decomposition into new holes.
