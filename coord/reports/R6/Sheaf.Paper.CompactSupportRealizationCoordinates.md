## What changed

Proved `WeilConjectures.CompactSupportFactorNormalization.integralComparison_normalization`
in the assigned module. The proof constructs an isomorphism from the actual
reconstruction unit, proper comparison and open reduction mate. The adjunction
Hom equivalence identifies its forward map with `integralComparison`; naturality
identifies its inverse with the existing `integralInverse` formula. Its inverse
laws and the reduction/counit normalization then follow without finite evaluation.

Added only proof imports and proved private categorical helpers. All existing
public signatures, definitions, attributes and public imports are unchanged.
Updated the owning node's proof route. No other existing module is changed.
The final module compiled through `lcompile.py` in 33.7 seconds with exit code 0.
The import-direction checks for the new proof imports passed.

## Proved and sorry left

Closed 1 of the original 3 holes:
`WeilConjectures.CompactSupportFactorNormalization.integralComparison_normalization`.
Added 0 holes and split off 0 statements.

The following original holes remain unchanged, both attached to
`lem-zl-compact-support-realization-coordinates-setup`:

- `WeilConjectures.CompactSupportFactorNormalization.ordinaryRestrictionSquare_existsUnique`.
- `WeilConjectures.CompactSupportFactorNormalization.ordinaryRestrict_kInjective`.

The first requires the sectionwise coefficient compatibility of the independently
normalized realization charts and completed coefficient presentation. The second
requires exactness of the corresponding localization left adjoint on arbitrary
schemes. Neither is asserted by the integral comparison proof.

## No longer needed

Removed the unused private proof import
`Sheaf.Paper.CompactSupportRealizationIdentity`.

For the integral normalization, the old planned direct dependencies
`lem-sf-generator-reduction-coherence` (`Sheaf.SixFunctors.GeneratorReductionStatement`),
`lem-sf-integral-open-reduction-comparison`
(`Sheaf.SixFunctors.IntegralOpenReductionComparison`),
`prop-weil-pbc-direct-image-limits` (`Sheaf.Paper.CompletedDirectImageLimits`), and
`lem-weil-pbc-constant-completion-equivalence`
(`Sheaf.Paper.ConstantCompletionEquivalence`) are replaced by the fixed open-mate
invertibility and unrestricted normalized reconstruction APIs. The proper factor
is already specified by `RealizationModel.push`; its adjunction formula suffices.
These nodes can still be needed transitively or by other consumers. No module is
withdrawn and no unit route is bypassed. Existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The general open-effectivity theorem asks for quasi-compactness, which is absent
from this statement. Its proved `fixedOpenReduction_isIso` helper needs no such
hypothesis. The open output's completeness is already in `Domain`, so unrestricted
normalized reconstruction supplies its unit isomorphism without adding a geometric
hypothesis. No statement correction is necessary.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
