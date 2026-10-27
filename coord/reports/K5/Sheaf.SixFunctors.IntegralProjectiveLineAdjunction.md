## What changed

Replaced the hole in `integralProjectiveLine_adjunction` by an explicit unit-counit
construction. The two supplied contraction formulas retain the supported diagonal
integrals; the proof uses the two integration fields to make the triangles identities.
The prescribed restricted functors and their preservation hypotheses are unchanged.
Added positive integral Tate comparisons and separate interfaces for the referenced
coefficient family, the normalized natural pair, and the contraction calculation.

## Proved and sorry left

The original declaration is reduced through genuine parts of its argument. This is a
decomposition, not a claim that the complete geometric argument is hole-free.
Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralProjectiveLine_adjunction`.
The item now has zero `sorry`. The delivery adds three named holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralNormalizedFamily_exists`
  (`lem-integral-normalized-family`): existence of the referenced coefficient family.
- `AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralUnitCounit_existsUnique`
  (`lem-integral-unit-counit-construction`): construction and naturality of the fixed pair.
- `AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralKernel_contractions`
  (`lem-integral-kernel-contractions`): the two calculations before applying integration.

Thus one original hole is closed and three are added: this packet is a decomposition
with net minus two holes closed, not a completed proof of the geometric adjunction.
The positive Tate comparisons, residue-unit construction, scalar cancellation, and
assembly into the adjunction contain no holes. No definition contains `sorry`.

A complete coefficient-family proof was attempted using the strict-system, completed
limit, and coefficient-extension declarations. The dependent conversion to
`IsDiagonalLimit` exceeded the 60-second file limit; experiments with its definition,
inline comparisons, and generic comparison lemmas are excluded from this packet.
There is no change to `DiagonalTowerTraceLimit` or its consumers.

## No longer needed

Removed the following direct proof imports from the item; the dependencies actually
needed for the component construction and contraction calculation are recorded on the
new nodes, so removing a direct import does not withdraw those mathematical results:

- `Sheaf.Paper.DiagonalTowerLimit`
- `Sheaf.Paper.DiagonalTowerCoefficients`
- `Sheaf.Paper.DiagonalTowerTrace`
- `Sheaf.Paper.IntegralProperProjectionFormula`
- `Sheaf.Paper.IntegralOpenImageProperFormulas`
- `Sheaf.Paper.FormalClosedSupportSheaves`
- `Sheaf.Paper.ProjectionSectionNormalization`
- `Sheaf.Paper.TraceBaseChangeFirst`
- `Sheaf.Paper.TraceBaseChangeSecond`

The native direct-image section comparison avoids the Brown compactification comparison
`det-prop-int-brown-construction` in this diagonal adjunction argument. No existing
source declaration or quarantined module is deleted. Experimental helpers not used by
the final proof are excluded from the packet.

## Where the brief, the DAG or earlier work was wrong

The original proof plan did not expose the naturality and endpoint comparisons needed
to connect the normalized integral diagonal formulas to the specified restrictions.
Those interfaces are now explicit. The completed limit characterization also has
expensive proof-irrelevance conversions when extracting its existential presentation;
compiler diagnostics, rather than mathematical weakness, motivated the local experiments.

## New nodes

`lem-integral-normalized-family` records existence of a whole-system referenced
coefficient family, in `Sheaf.SixFunctors.IntegralNormalizedFamily`.

`def-integral-kernel-tate-comparisons` records the three proved positive integral Tate
comparisons, in `Sheaf.SixFunctors.IntegralKernelTateComparison`.

`def-integral-kernel-unit-counit` fixes the types and component normalizations, in
`Sheaf.SixFunctors.IntegralKernelUnitCounit`.

`lem-integral-unit-counit-construction` asserts the unique normalized natural pair, in
`Sheaf.SixFunctors.IntegralKernelUnitCounit`.

`lem-integral-kernel-contractions` states the two contractions before integration, in
`Sheaf.SixFunctors.IntegralKernelContractions`.

The file-local proof commands and unchanged consumer interfaces are documented in
`coord/changes/integral-projective-line-proof-scope.md`. No existing public signature,
definition, or public import is changed.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
