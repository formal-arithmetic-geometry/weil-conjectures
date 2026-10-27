## What changed

Filled `WeilConjectures.sections_rational_model_comparison` with its statement
unchanged. The proof constructs the tensor/carrier natural isomorphism explicitly,
lifts it to complexes and derived categories, and applies the point-fibre
normalization. A private cohomology argument reflects the resulting carrier-lifted
isomorphism to the small derived category, using the existing field-complex
cohomology splitting theorem.

For ordinary sections, a strict integral direct-image model supplies the integral
linear functor. Its reconstruction and uniqueness of the direct-image Roos vertex
compare its values with `integralImage`. Semilinear scalar localization then maps
the supplied rational representative isomorphism. For compact sections, the
existing compact-support finite action and its object normalization do this
transport directly. All added imports are private proof imports. The node's proof
and dependencies now record these constructions.

The private Roos comparison follows the argument of `purPushTowerIso` in
`OrdinaryAdjunctionScalarCompatibility`. That helper is present in the shared
source but was absent from the compiled environment inspected during this session.
The proof here uses the available private helpers of
`SfCompleteDirectImageReduction` and `SfDerivedCompleteLegacyComparison` instead.
No declaration of those modules was changed.

## Proved and sorry left

Closed the one existing hole in
`WeilConjectures.sections_rational_model_comparison`. No holes are added or split
off, and no `sorry` remains in the delivered module. The proof uses existing
stated dependencies, including `strictDirectImageIntegralModel`; it does not
claim to remove holes inside those dependencies.

## No longer needed

No original public import was removed. No module is withdrawn. The direct call to
`lem-weil-l-adic-integers-localization-uniformizer` in the old proof plan is
unnecessary: exactness and normalization of the coefficient extension are already
provided by `FiniteCoefficientPoint`. This does not claim that the uniformizer
lemma is unused by those existing constructions. All the other original planned
interfaces remain needed.

## Where the brief, the DAG or earlier work was wrong

The original plan spoke of applying a rational ordinary direct-image functor,
while `rationalImage` itself specifies only objects. The strict integral model,
scalar-localized functor and Roos comparison supply that functorial transport
without changing the definition. The arbitrary prescribed complex P needs an
explicit tensor/carrier interchange; no boundedness, finite freeness or
perfectness assumption on P is used. Zero, torsion and shifted complexes require
no exceptions.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
