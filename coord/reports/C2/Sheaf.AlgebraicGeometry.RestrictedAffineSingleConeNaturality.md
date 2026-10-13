## What changed

Completed the proof of
`AlgebraicGeometry.Etale.restrictedAffineSingleConeIso_naturality` in
`Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeNaturality`.
The statement, definitions, visibility and imports are unchanged.

The proof follows the node's route. Three applications of `upperStarComp_assoc` prove
compatibility of the two projection squares with the cone triangle. Naturality of the
composition comparisons and `hH` then give the coefficient-level equation. A degreewise
proof shows compatibility of `mapCochainComplexSingleFunctor` with composition comparisons;
naturality of that comparison lifts the coefficient equation to complexes. All five private
categorical helpers are proved. No intermediate theorem is left for another item.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Etale.restrictedAffineSingleConeIso_naturality`
(node `lem-sbc-restricted-affine-single-cone-naturality`).
No holes added; no `sorry` remains in the delivered module. This is a proof, not a decomposition.

## No longer needed

None. The existing import `Sheaf.AlgebraicGeometry.RestrictedAffineSingleMaps` is required
by the statement and its explicit constructions. The inverse-image composition dependency
is used through that import. No planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped because `RestrictedAffineSingleMaps.olean` was unavailable.
An unchanged local copy of that dependency was compiled for initial experiments; the published
library now contains it, and that copy is not part of this delivery. No dependency interface
was changed. The DAG's proof plan is sufficient and is followed unchanged.

## Second reading by C2

1. **Interface and accidental changes.** Compared the delivered module with the repository
version. The target statement, all existing declarations, visibility, and the public import
are byte-for-byte unchanged; only private proof helpers and the target proof were added.
Verdict: pass.

2. **Proof and trust basis.** The delivered source contains no `sorry`, `axiom`, `unsafe`,
`opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The proof is composed of
categorical cancellation, naturality, and degreewise homological-complex extensionality.
The local compiler was attempted; its process waited for the shared compile slot and timed
out without emitting a diagnostic, so the delivery tool's compilation check is required.
Verdict: pass subject to the delivery compile check.

3. **Statements and split-offs.** No theorem was split off and no statement was added or
changed. The sole target is proved directly from the existing definitions and the two DAG
proof dependencies. Verdict: pass.

4. **Pruning and route.** The proof uses the existing `RestrictedAffineSingleMaps` import,
including the inverse-image composition comparisons and explicit restricted constructions.
No imported module or planned proof dependency is unused, and no unit route is bypassed.
Verdict: pass.

5. **DAG agreement.** The target's node already records the same statement, proof route,
proof dependencies, source, and realized unit route. Since this delivery adds no declarations
or nodes, no DAG edit is needed. Verdict: pass.

I changed only this report by adding this second-reading record; the Lean module and DAG
remain otherwise unchanged.
