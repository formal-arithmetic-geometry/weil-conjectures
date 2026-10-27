## What changed

Proved `WeilConjectures.purAdicScalarExtensionTorBound`, preserving its entire signature
and both public imports. Its two private proof imports are now
`import all Sheaf.Paper.AdicCoefficientDatum` and
`import all Sheaf.SecSmoothPurity.ScalarExtensionFunctor`.
The proved private helper `completedScalarReductionComparison` composes the existing
derived-composition comparisons around the coefficient square. The main proof applies
the existing `AlgebraicGeometry.ProEtale.scalarExtension_tor` at the same positive
level, then transports the universal representative test across that comparison.
Updated the existing node's proof, proof dependencies and proof origin accordingly.
No definition, instance, public declaration signature, source-library file, or consumer changes.

The original natural-language docstring describes the longer planned tower argument;
the actual shorter argument is recorded in the updated node and the private helper.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.purAdicScalarExtensionTorBound`
(node `lem-pur-adic-scalar-extension-tor-bound`).
Proved the new private helper `WeilConjectures.completedScalarReductionComparison`.
Zero `sorry` remain in the delivered module; zero holes added; zero split off.
The previously compiled reduction was strengthened by proving its coefficient-square
comparison from the already proved `derivedReductionComposition`, rather than leaving
a new statement. The exact interval, arbitrary target levels, and all test modules remain.

Validation: the comparison and main theorem compiled together before consolidation;
the final single-file compile and delivery checks are recorded by the tools.
Edge cases checked against the actual argument: index zero means exponent one;
identity field inclusion gives the identity coefficient square; ramified inclusions
still have a same-exponent quotient map; zero and empty-scheme objects require no
special handling; a=b retains its exact interval. Neither hK nor the ramification
witness is mathematically needed for this stronger argument, but both remain in the
unchanged signature. No finite-type or invertibility assumption was added on W.

## No longer needed

Removed these direct private imports:
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Paper.SfIntegralConstructible`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The item no longer directly uses the planned proof dependencies
`def-weil-derived-complete-integral-detailed`, `def-weil-derived-tensor`,
`def-weil-finite-tor-amplitude`, `lem-coef-normalized-dvr-effectivity`,
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`,
`lem-pur-kflat-change-of-rings`, and
`lem-weil-integral-scalar-extension-constructible`.
The existing generic scalar and composition theorems encapsulate the necessary
K-flat algebra. Uniform Tor vanishing at each level needs no reconstruction,
completeness, or constructibility theorem. Dependencies still occurring in the
unchanged statement or through the retained library theorems remain needed there;
this delivery withdraws no modules and claims no globally pruned modules.
Both original public imports are retained because they provide the unchanged interface.

## Where the brief, the DAG or earlier work was wrong

The original plan's reconstruction step proves more than this theorem concludes.
Its pointwise Tor conclusion follows before reconstructing any tower. Also the existing
integer inclusion already gives a map at equal positive exponents, so choosing a
ramification-index-dependent cofinal level is unnecessary. These are simplifications,
not statement corrections or changes to the unit route. The two generic facts used
were found already fully proved (private) in the published modules and are accessed
by private `import all`, without editing their owner modules or introducing new nodes.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
