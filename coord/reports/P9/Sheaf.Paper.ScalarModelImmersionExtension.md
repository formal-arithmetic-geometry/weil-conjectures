## What changed

Filled `AlgebraicGeometry.ProEtale.scalarModelImmersionExtension` using a private proof valid for every commutative condensed ring. Existing public signatures and definitions are unchanged. Added private proved helpers for the identity-cover zero model, closed-operation scalar transport, and property-generic reindexing of the existing complementary stratifications. The actual source strata, covers and scalar presentations are retained.

Repaired the return at head `7b4d466766b`: removed the duplicate private theorem `local_model_iso`. A private `import all Sheaf.Paper.IntegralContinuousCokernelLocalModel` makes the already proved `AlgebraicGeometry.ProEtale.ContinuousRingUniverse.model_of_iso` available, and the old-stratum model construction now applies it directly. Its explicit binders match for every commutative condensed ring and every scheme; no integral-coefficient hypothesis is needed. The import is acyclic, and the integral cokernel theorem itself is not used. The existing node records this helper use. The current repository still has the same public assertion definition and theorem signature as the retained packet; only the four already permitted proof-route fields of the node differ.

The extended stratifications come from `Scheme.noetherian_complementary_stratifications`. A private adapter adds their constructibility proofs without changing their domains or maps. Their last-indexed complementary stratum is identified with `none` by `finSuccEquivLast`, after the supplied index equivalence.

The closed-operation argument uses `ringSheaf_closed_localization` as a generic tool: its linear module functor is identified with `CondensedRing.linearLowerStar`, and `comapPullbackHomCompIso` transports along the coefficient scalar equivalence. This avoids reconstructing section-ring sheaves. The unit's extension-by-zero route stays intact. The DAG proof and proof dependencies are updated to match. The static gate also requires a record for the file-local elaboration commands: `coord/changes/P9-scalar-model-immersion-proof-context.md`. Its consumer inventory has two unchanged transitive importers and no external use of either public declaration.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.scalarModelImmersionExtension` (node `lem-sfb-scalar-model-immersion-extension`). Added zero holes; zero holes remain in this module. This is a proof from existing declarations, not a decomposition. All retained private helpers are proved; the removed duplicate helper is replaced by an existing proved theorem. Existing dependencies retain their own independent proof status. The repaired complete module compiled with `lcompile.py` in 6.2 seconds, exit code 0; delivery preflight supplies the final verification.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.Topology.NoetherianSpace`, and `Mathlib.Topology.Constructible`. Replaced the direct finite-stratification interface import with the geometric theorem that publicly supplies it.

This proof does not use `lem-weil-pbc-proetale-ringed-open-closed` or `lem-sfb-internal-module-operations-transport`: internal ring-sheaf localization and scalar transport already give the required closed operations, and the source library supplies open operations. It does not use `lem-sfb-scalar-model-restriction-criterion`: the original model witnesses are transported directly along pullback composition on the supplied extended strata, avoiding that criterion's additional rigid heterogeneous-equality input for a first-indexed complementary stratum. These three nodes are removed from this node's proof dependencies; the two corresponding obsolete tool approvals are withdrawn. The duplicate `local_model_iso` declaration is also no longer needed and is removed; its transport result comes from the existing `ContinuousRingUniverse.model_of_iso`. No module is withdrawn and no adopted source declaration is changed. The `CartesianCoefficients` public import remains for the coefficient objects in the statement, although the specialized cartesian-coefficients assertion is not used as a proof lemma.

## Where the brief, the DAG or earlier work was wrong

The returned packet unnecessarily duplicated an existing coefficient-generic local-model isomorphism theorem; the repair reuses that theorem with a private import.

The previous plan is mathematically sound but its Lean interfaces do not compose directly: the geometric lemma gives an arbitrary index equivalence with a last complementary stratum, while the restriction criterion requires heterogeneous equality with a fixed first-indexed one. The delivery uses the geometric lemma directly and proves its elementary last-index-to-option reindexing. Profiling localized an initial 60-second timeout to instantiating a dependent-pair property with the coefficient model predicate. A private helper performs reindexing for an arbitrary property of a scheme and its map before specializing to the model predicate; the repaired complete file compiles in 6.2 seconds without raising any limit. The ringed sectionwise comparison route is also longer than the existing internal ring-sheaf localization API. No statement repair was needed. Empty source strata, empty complementary schemes, nonreduced closed schemes, and the zero coefficient ring are covered by the same construction without extra assumptions.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
