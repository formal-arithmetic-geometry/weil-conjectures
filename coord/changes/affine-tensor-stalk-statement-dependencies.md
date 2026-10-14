# AlgebraicGeometry.affineTensorPullbackHomologyStalkIso_counit_coordinate

## Reason

Repair C6 from reviewer X-8fbc1: the main coordinate node now uses the pointwise
helper, so the helper cannot cite the main node as a statement dependency.
Its statement uses the affine base-change coordinates, the derived cohomology
presentation, the tilde pullback comparison, and stalk localization directly.
The former node description only said "the displayed equation" and relied on the
parent reference. It is now a standalone description of exactly that same
pointwise equation, citing the four requested dependencies. The accompanying
`statement_change` record preserves the old description, dependencies and proof
metadata and checks every base citer. This clarification changes no mathematical
claim and leaves every Lean statement unchanged.

## Old

Node description, verbatim: The displayed affine tensor pullback stalk coordinate equation for each localized class y.

```json
"stmt_deps": ["lem-pc-affine-tensor-pullback-stalk-coordinates"]
```

## New

Standalone node description (the same mathematical equation):

For commutative rings A and A', a ring map phi:A to A', a cochain complex M of A-modules, a
representative isomorphism e:Q(tilde M) to K, an invertible ordinary pullback counit on tilde M, a
degree i and a prime p of A', suppose the derived pullback L of K has quasi-coherent cohomology.
Write b for the canonical affine base-change cohomology isomorphism
[def-pc-affine-base-change-tilde-coordinates] and t for the localized ordinary tensor cohomology
to pullback stalk coordinate constructed from the tilde tensor-pullback comparison
[lem-weil-pbc-tilde-pullback-base-change] and tilde stalk localization
[lem-weil-pbc-spec-tilde-stalk-localization]. For every localized cohomology class y, the
canonical derived cohomology stalk coordinate [lem-pc-affine-derived-cohomology-presentation] of
the localization of b(y) equals the stalk of H^i of the derived pullback of e, applied to the
stalk of H^i of the inverse counit applied to t(y). This is the unchanged pointwise
counit-coordinate equation; no main coordinate theorem is assumed.

```json
"stmt_deps": [
  "def-pc-affine-base-change-tilde-coordinates",
  "lem-pc-affine-derived-cohomology-presentation",
  "lem-weil-pbc-tilde-pullback-base-change",
  "lem-weil-pbc-spec-tilde-stalk-localization"
]
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTensorPullbackStalkCoordinates | T4 | Dependency cycle removed; Lean statements unchanged. |

The helper node
`new-lem-pc-affine-tensor-pullback-stalk-coordinates-at` also receives the standalone
statement description and its required clarification record. The main node's
proof dependency on this helper remains correct.

## Status

landed 20261014T043533-L-1336322 2026-10-14 (merge of deliver/T4/Sheaf.Algebra.Homology.AffineTensorPullbackStalkCoordinates)
