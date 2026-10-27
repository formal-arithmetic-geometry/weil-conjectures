## What changed

Proved `AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.target_properties`
in `lean/Sheaf/Paper/CoordinateTowerNormalizationInduction.lean`. Four proved private
theorems and a constructed private comparison helper establish finite-Tor constructibility of the shifted ordinary finite Tate line,
construct an ordinary origin by ordered tensor induction, identify that origin with the
existing Tate target, and transport constructibility and Tor amplitude to the canonical
`Rnu_*` antecedent. The proof uses the actual comparison counit.

Added proof-only imports of `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`,
`WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift`,
`WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison`, and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin`.
Updated the existing node's first proof step and dependency list to record this route.
All public signatures, definitions, and public imports are unchanged.
Local irreducibility annotations keep the large concrete functors from unfolding
while checking the new proof and the subsequent endpoint constructions.

## Proved and sorry left

Closed one current hole:
`AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.target_properties`
(node `lem-pur-coordinate-tower-normalization-induction`).

One current hole remains unchanged:
`AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.coordinateTower_normalization_induction`
(the same node). No holes were added; no statements were split off.

The three construction equalities `zero_successor`, `thetaStepRaw_target`, and
`projectionGammaRaw_target` were already proved by K4 in the current shared source;
this delivery does not count them as new closures.

## No longer needed

No import or module is removed from the current shared source. The coefficient proof does not need `Sheaf.Paper.PurTwistSheafLocallyFree` or node
`lem-pur-twist-sheaf-locally-free`: the ordinary finite line's own local trivializations
supply the exact constructible and flat object used by the target. Its obsolete tool-use
entry is removed, along with the unused intrinsic-origin tool-use entry. The
comparison counit criterion supplies the origin fact directly in the fixed-scalar
category. `Sheaf.Paper.FiniteTorAmplitudeSites` and
`Sheaf.Paper.ProEtaleConstructibleOrigin` need no direct proof imports; the existing
public dependencies already expose the categories used in the unchanged statements.
No public import or module is withdrawn. The remaining main-induction dependency
plan is retained.

## Where the brief, the DAG or earlier work was wrong

At session start the shared source still showed five holes while the node recorded
K4's three construction proofs. The source caught up during the session; this packet
is based on the current two-hole source and closes only `target_properties`.

The DAG's coefficient step described the completed integral Tate-line theorem, whose
module-valued interface differs from the actual ordinary finite line used here.
The finite-etale-twist theorem supplies a direct proof on the correct object.
Explicit coefficient finiteness witnesses prevent expensive typeclass searches.
The optimized file compiled through `lcompile.py` in 47.9 seconds; profiling
was removed before delivery.

The proof covers r=0, the lowest positive coefficient level, and the empty scheme;
it assumes no nonemptiness or general smooth-purity theorem.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
