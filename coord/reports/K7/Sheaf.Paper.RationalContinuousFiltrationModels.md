## What changed

Filled `rationalContinuousFiltrationModels` in
`Sheaf.Paper.RationalContinuousFiltrationModels`, retaining its statement and public imports.
The proof applies the finite free criterion and the existing stratum integral-model theorem.
It transports the given filtration by inverse coefficient restriction and constructs each
integral model as the specified degree-zero complex, using its supplied completed membership.
Private proved helpers construct the coefficient encoding, identify finite coefficient maps
from their constant normalization, recover the integral scalar square from all finite
projections, and compare exact scalar extension with the derived single functor.
The resulting quotient isomorphism composes the actual scalar comparison, beta, the stratum
cokernel identification, and preservation of cokernels. No existing definition changes.
Proof imports open the existing private APIs in
`IntegralCoefficientCompletenessTransport` (restriction equivalence),
`RationalModuleRealizationFunctor` (finite constants),
`ContinuousCoefficientCompletion` (the constant-sheaf unit), and `AdicCoefficientDatum`
(the ordinary tensor object equality). Mathlib's `DerivedCategory.ExactFunctor` and
`Limits.Preserves.Shapes.Kernels` provide the single-functor and cokernel comparisons.
The node proof records this assembly and these existing dependencies.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousFiltrationModels`
(node `lem-per-rational-continuous-filtration-models`). No holes added or split off.
Single-file validation through `lcompile.py` passed cleanly in 18.1 seconds.
No `sorry` remains in the delivered module. The existing dependency
`RationalStratum.exists_filtration_integral_models` remains an imported theorem;
its proof is outside this delivery.

## No longer needed

None. Both declared proof dependencies, their imports and the original unit route are
retained. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The normalized coefficient transport in the earlier node's
"elementary" steps requires explicit finite constant-sheaf uniqueness, inverse-limit
extensionality and scalar-adjunction comparisons; these are proved privately here.
The rework record's archived module was read; the current source is present, and the
original declaration and attachment are retained.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
