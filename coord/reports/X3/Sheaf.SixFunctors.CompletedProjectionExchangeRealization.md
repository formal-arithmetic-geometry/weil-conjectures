## What changed

Proved `WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeRational`
and `WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeCommonStage`
in `Sheaf.SixFunctors.CompletedProjectionExchangeRealization`, without changing any existing
signature or definition. The rational proof derives the required finite-Tor hypothesis from
`integral_residue_tor` and extracts the rational conclusion of the integral theorem. The
common-stage proof applies the inclusion functor's map to that rational equality.

Added the private proof import `Sheaf.Paper.DirectImagesConstructible` for the proved
`finiteFieldDatumPrimeUnit` lemma. Its only additional module beyond the original import
closure is DirectImagesConstructible itself, which has no holes. Retained the private import
`Sheaf.Paper.IntegralResidueTor`. All public imports are unchanged.

Validation: the final sandbox module compiled successfully through `lcompile.py`
(exit code 0, 21.8 seconds), with no compiler warnings.

This is a partial delivery: the main integral/system theorem remains the next obligation.
The DAG's final step now records the concrete residue-Tor and inclusion-map argument.

## Proved and sorry left

Closed 2 of the original 3 holes, with no holes added and no decomposition:

- `WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeRational`.
- `WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeCommonStage`.

One original hole remains:

- `WeilConjectures.CompletedProjectionExchange.completedProjectionExchangeRealization`
  (node `lem-sf-completed-projection-exchange-realization`). Its complete original proof
  plan and source remain in the docstring and DAG. No partial tactic proof replaces it.

The new proofs are conditional on this existing integral theorem, as intended for stage 3.

## No longer needed

The two field-stage proofs do not use
`lem-sf-pf-coefficient-realization-transport` / `Sheaf.Paper.CoefficientRealizationTransport`:
the displayed rational and common-stage arrows are already literal functor images.
Removed that dependency from the node's final proof step, `proof_deps`, and top-level
`tool_uses` approval list.

Removed these unused private proof imports from the item:

- `Sheaf.Paper.SfDirectImageCTFEtaleOrigin`.
- `Sheaf.Paper.SfDirectImageCTFNonproper`.
- `Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound`.
- `Sheaf.Paper.CompactSupportNormalizedRealization`.
- `Sheaf.Paper.ProEtaleScalarMateNormalization`.
- `Sheaf.Paper.ProperEtaleOriginScalarIsomorphism`.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`.
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`.
- `Sheaf.Paper.SystemNormalizedTensorClosure`.
- `Sheaf.Paper.ComparisonTorAmplitude`.
- `Sheaf.SixFunctors.FiniteCoverCTFLocality`.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`.
- `Sheaf.Paper.OpenFiniteConstructibilityInterval`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.
- `Sheaf.Paper.CoefficientRealizationTransport`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.PullbackTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientTensorCtf`.
- `Sheaf.Paper.NormalizedEtaleOriginWitnesses`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.

Apart from coefficient transport, these modules still describe dependencies of the
unproved main theorem's retained plan; this delivery does not claim they are globally
unnecessary. Their direct proof imports can be restored when the main proof uses them.
No module is withdrawn, and no unit statement or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The final DAG step's abstract coefficient transport is
unnecessary for the actual field-stage signatures: `rationalLeft`/`rationalRight` are
localization images, and the common-stage theorem explicitly asks for their inclusion
images. Residue Tor handles the rational theorem's constructible second input; the
prime-unit lemma supplies its residue-field instance. Zero objects, empty schemes,
identity squares, and ramified coefficient fields require no extra hypotheses in these
proofs. No reduction functor out of a rational field or faithfulness argument is used.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
