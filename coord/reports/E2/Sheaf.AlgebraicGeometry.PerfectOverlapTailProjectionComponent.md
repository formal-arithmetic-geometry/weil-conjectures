## What changed

Revalidated the complete proof of
`AlgebraicGeometry.perfectOverlapTailProjectionComponent` and reduced its proof
imports. Prove the two geometric projection equations directly using Mathlib's
`morphismRestrict_homOfLE` and the pasted cartesian square's
`isoPullback_inv_fst`, rather than passing through the auxiliary transported
scheme-isomorphism API. Reuse the existing core transport theorem
`perfectOverlapCompositeLocalIso_eq_compositionTo_global` for the local
composition equation.

The rest of the proof still combines the nested-square comparison,
`compositionTo_prism`, the stage-object component equations and
`perfectOverlapProjectionCompositeAbstract`, followed by naturality and Boolean
elimination. Update the proof explanation and the existing node's proof and
proof_origin. Preserve the exact theorem statement, both public imports, the
node attachment, all seven declared dependencies, and the unit realization route.

The change record is
`coord/changes/E2-perfect-overlap-tail-direct-projection.md`. Read the quarantined
parent `PerfectOverlapProjectionCompositionComponent`; its application remains
valid against the identical theorem signature. No consumer adaptation is needed.

## Proved and sorry left

This is a zero-hole rework and proof-dependency cleanup. The current shared source
already contained the complete theorem and N2's earlier redundant-attribute repair.
The original source compiled before edits in 20.5 seconds. The revised argument
with all four proof imports removed compiles without warnings in 21.7 seconds.
The delivery tool performs the final compile and axiom checks.

`AlgebraicGeometry.perfectOverlapTailProjectionComponent`, node
`lem-pc-perfect-overlap-tail-projection-component`, remains completely proved.
Holes closed: zero of zero. Holes added: zero. Holes left: zero. No statement is
split off; no new declaration, definition, or node is introduced.

## No longer needed

Removed these four private proof imports:

- `Sheaf.AlgebraicGeometry.PerfectOverlapStageSchemeIso`: the geometric projection
  equations are now derived directly from Mathlib. Its declarations are unused.
- `Sheaf.AlgebraicGeometry.PerfectOverlapRestrictedComposition`: use the existing
  local-composition equation from the core transport API instead. Neither theorem
  of this auxiliary module is needed by the revised proof.
- `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare`: redundant direct
  import; its declarations remain used and publicly supplied by the stage tail.
- `Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence`: redundant direct
  import; its declarations remain used and publicly supplied by the stage tail.

The first two modules have no other live importers in either library root; the
only additional textual importers found are the preserved quarantine archive of
this item. This prunes the item's dependency edges, with no module withdrawals.
No DAG node is discarded: the seven declared dependencies are still needed by
the theorem statement or its proof. No adopted-source declaration is changed.

Lean Finder returned restriction and pullback projection equations; Loogle
returned naturality. Project searches found the existing core transport local
composition theorem and the two prism lemmas. These supply the shorter geometric
route without introducing any intermediate obligations.

## Where the brief, the DAG or earlier work was wrong

The rework row describes the failure of an older cluster restoration. The current
source already has the previous repair and zero holes; it does not reproduce
that failure. This delivery does not claim an additional repair of that historical
attribute error or a new hole closure. It makes a concrete proof change and
prunes two auxiliary proof dependencies instead of resubmitting an unchanged file.

The old node proof described the transported-isomorphism projection helper. Its
updated second step records the direct Mathlib calculation, and its third step
names the existing core transport equation. Empty and equal opens require no
extra assumptions: restriction naturality and pullback projection equations hold
for all opens. No statement changes, disputed statements, or new edge cases arise.
The quarantined parent remains a dependency consumer and is not withdrawn.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
