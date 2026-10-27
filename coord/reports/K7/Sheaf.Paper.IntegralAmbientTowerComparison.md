## What changed

Filled all six proof bodies in Sheaf.Paper.IntegralAmbientTowerComparison, preserving all
existing signatures, definitions and public imports. The coefficient-model and encoding
clauses apply the stated realization theorem. The coefficient resolution is the cone of
the short exact multiplication/quotient sequence. Private proved helpers establish the
Roos-object isomorphism, transport Roos triangles, obtain countable products, and use the
existing constant-presentation completion reflector to detect the specified completion unit.
The main comparison applies the already normalized CompletedDirectImageLimits API.
The etale-origin clause composes the three prescribed isomorphisms.
Updated the node proof and proof dependencies to this shorter route. No new public interface.
The proof context uses transparency settings compatible with the existing coefficient
models. Removed the obsolete hasDerived instance-disable command attached to the removed
private completed-pushforward import. The existing public imports remain verbatim.
Change record: coord/changes/K7-integral-ambient-tower-proof-context.md.
The consumer check reports zero current downstream Lean modules; DAG parents keep
the same interface. No forced adaptation is needed.

## Proved and sorry left

Holes closed (6 of 6), all in node lem-sfb-integral-ambient-tower-comparison:

- AlgebraicGeometry.Scheme.IntegralAmbientTower.finiteResolution
- AlgebraicGeometry.Scheme.IntegralAmbientTower.coefficientModel_exists
- AlgebraicGeometry.Scheme.IntegralAmbientTower.encodings
- AlgebraicGeometry.Scheme.IntegralAmbientTower.complete_iff
- AlgebraicGeometry.Scheme.IntegralAmbientTower.comparison
- AlgebraicGeometry.Scheme.IntegralAmbientTower.etaleOriginComparison

Holes added: zero. Holes left in the delivery: zero. The proof uses existing stated
results, including integral_coefficient_model_realization and koszul_quotient_reflector;
their existing holes are not claimed as closed here. No split-off theorem or new module.

Validation: lcompile.py compiled the item cleanly in 32.8 seconds on the project server.
The delivery tool performs the required independent compile and declaration-axiom probe.

## No longer needed

Removed proof imports:

- Sheaf.Paper.CoefficientSystemDerivedComparison
- Sheaf.Paper.CompletedCoefficientPushforwardComparison
- Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
- Sheaf.NumberTheory.Padics.IntegersProfiniteTower
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.Paper.AugmentedDiagramProjectionMate
- Sheaf.Paper.CompletedConstantSheafReduction
- Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
- Sheaf.Paper.ReductionPullbackDerivedTower
- Sheaf.Paper.PerfectProjectionFormula

The old planned dependencies lem-sfb-integral-quotient-resolution-normalization and
lem-sfb-quotient-system-projection-lift are not directly needed by this module: the scalar
resolution is elementary, and the normalized strict projection theorem already exists in
CompletedDirectImageLimits. The realization theorem may still depend on the resolution
normalization; no global withdrawal is claimed.
The completed-coefficient pushforward comparison,
constant-tower pushforward normalization and direct perfect-projection applications are
unnecessary here because the existing adic direct-image API proves those normalized facts
in exactly the required coordinates. The bounded-below mate theorem supplies the optional
etale clause directly. Old unused tool_uses approvals were removed, preserving retained order.
The RingedTowerPushforwardLimitComparison import and dependency are retained to preserve
the protected unit route. No library module or declaration is withdrawn. The unit route is retained: completeness,
perfect finite reduction, strict compatibility and bounded-below etale origin all remain.

## Where the brief, the DAG or earlier work was wrong

The DAG plan predated the proved adic direct-image API. Its separate varying-ring lift and
completed-coefficient reconstruction applications duplicate facts already supplied by
AdicCoefficientDatum.towerProjection_properties, towerProjection_isIso and push_complete.
The Roos condition alone need not identify the specified map to a limit; the proof instead
uses object isomorphism to transfer the complete locus via the existing completion reflector,
and then proves invertibility of the specified unit. This avoids asserting faithfulness of
derived tower evaluations or uniqueness of arbitrary triangulated cone fillers.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
