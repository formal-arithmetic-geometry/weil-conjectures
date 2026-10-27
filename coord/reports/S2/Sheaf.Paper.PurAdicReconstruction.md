## What changed

Repair of returned head `4e9d00afc5f` (reviewer `C-4e9d0`): the mathematical review
passed, but landing rejected an `--apply-fixes` path naming only
`Sheaf.Paper.PurAdicReconstruction.md`. The report in the delivery is
`coord/reports/S2/Sheaf.Paper.PurAdicReconstruction.md`; any report correction must
use that full repository-relative path. This sandbox's `report.md` is packaged there
by `deliver3.py`. There is no root-level report with the rejected basename.
Refreshed the node from current shared sources, retaining only this delivery's
`proof`, `proof_deps`, `proof_origin` and `tool_uses` changes. The delivery tool builds
the replacement commit on current `origin/sheaf-dag` and reruns compilation/preflight.
The reviewed Lean proof is retained, with no change to its mathematical interface.

Filled `WeilConjectures.purAdicReconstruction` without changing its signature or any
public definition. The proof applies the declared source-finiteness and normalized-purity
lift theorems, proves the lift invertible by exact evaluation and homology, and composes
its total-limit image with the actual completion unit. The existing
`purNormalizedReconstruction` proves that unit invertible after the recorded coefficient
presentation comparison. The reduction equation is proved by transposing under the
finite scalar adjunction and using its actual unit/counit projection normalizations.
Two proved private helpers transport completeness and integral finite-Tor finiteness.
The public signatures and the restricted-evaluation definition are unchanged;
there are no changes under `lean/WeilConjectures/`.
The item node's proof, dependencies and origin now describe this Lean argument.
On resumption, comparison with the current source confirmed that the theorem signature
and public definition are identical. A profiled compile passed in 42.0 seconds; direct
projections now avoid destructuring unused clauses of the large source/lift results.
The heartbeat setting has its required explanatory comment and profiling is removed.

Proof imports added: `AdicPuritySourceFiniteness`, `AdicNormalizedPurityLift` (with
private body access for its no_expose evaluation composites),
`AdicPurityExceptionalReduction` (private body access for the specified target reduction),
`PurNormalizedReconstructionAdjunctionCalculus`, `IntegralCoefficientCompletenessTransport`,
and `SfIntegralConstructibleTriangulated`, all under `Sheaf.Paper`. A proof-only `import all Mathlib.CategoryTheory.Limits.HasLimits`
and `import all WeilConjectures.Compactification.Defs` expose the canonical limit-cone
and compactification definitions needed to identify the two completed-scalar
presentations; no library definition is changed.

## Proved and sorry left

Closed one hole: `WeilConjectures.purAdicReconstruction`
(node `thm-pur-adic-reconstruction`). Zero holes remain in the item; zero holes added;
zero statements split off. The imported source-finiteness theorem still has its own hole;
the current normalized-lift theorem is proved from its dependencies. This is a proof
from their declared interfaces, not a
claim that their transitive axioms have already been eliminated.

## No longer needed

The direct planned dependency `lem-pur-adic-roos-realization-reductions`
(`Sheaf.Paper.AdicRoosRealizationReductions`) is replaced by the existing actual-unit
normalized reconstruction theorem `lem-pur-normalized-actual-reconstruction-maps`.
Its canonical projection equations come from `lem-coef-derived-system-evaluation-calculus`.
The tower-map isomorphism criterion is proved directly using derived homology and exact
component evaluation. The direct `lem-weil-integral-ctf-triangulated` dependency is
replaced by existing closure of `sfIntegralConstructible` and a direct transport of the
same uniform Tor interval along reduction of the isomorphism.

Removed direct proof imports (their mathematics may remain in the transitive closure
of the retained source-finiteness/lift declarations; no module is withdrawn):

- `Sheaf.Paper.NormalizedDVRTower`
- `Sheaf.Paper.SmoothPurityMap`
- `Sheaf.Paper.FiniteTorAmplitude`
- `Sheaf.Paper.IntegralExceptionalInverseImage`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.FiniteCoefficientSmoothPurity`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.TwistPreservesFiniteness`
- `Sheaf.Paper.FiniteReductionOfPurity`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.IntegralCtfTriangulated`
- `Sheaf.CategoryTheory.SequentialTowerEvaluationFull`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.FiniteTorAmplitudeSites`

All old top-level `tool_uses` approvals are removed from this item's node, since these
were the former expanded direct route: integral operation preservation, twist preservation,
pullback Tor amplitude, sequential tower evaluation fullness, ringed strict tower homotopy
limits, levelwise derived-limit isomorphisms, integral CTF triangulation, normalized DVR
effectivity, exact scalar restriction, derived change of rings, and derived adjoint functors.
The source-finiteness and normalized-lift nodes retain their own dependencies on those
facts. No claim that they become globally unnecessary is made. A consumer search found
no other active parent citing the Roos-realization node; `IntegralCtfTriangulated`
continues to have other consumers and is only removed from this direct proof.

## Where the brief, the DAG or earlier work was wrong

The DAG's generic Roos-realization theorem constructs an existential comparison `e`;
the item requires the specified completion unit in the formula for gamma. The existing
`purNormalizedReconstruction` already proves invertibility of precisely that unit and
retains all the required projection normalizations. It supplies a shorter route with
no new lemmas or hypotheses. The finite-purity lift and actual source-finiteness stages
are retained. The previous documented unit-route correction in `split_report.unit_error`
is preserved, and no unit/chapter statement or route is changed.

The latest blueprint has reorganized this sketch (the old standalone adic reconstruction
proof path is absent). Its current coefficient-change proof, part (1), explicitly uses the derived-limit
realization of the finite purity maps, normalized reconstruction, and recovery of the
finite maps by the counit-transpose comparison. That is the route followed here. The
preserved node records the earlier reviewed normalized-DVR refinement.

Searches actually run: LeanFinder for compatible finite-coefficient adic purity returned
ordinary adic-ring/completion facts, no sheaf purity match; Loogle confirmed
`CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃`; the remote grep query found no full
match. Local searches found the actual-unit theorem and exact Hom normalization fields.
These are existing general tools; the coefficient-presentation completeness comparison
is used only to identify the completeness predicate, without changing the unit route.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
