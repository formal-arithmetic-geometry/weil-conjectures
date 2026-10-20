## What changed

Proved all seven original obligations in
`Sheaf.AlgebraicGeometry.SupportedExteriorProduct`. The ordinary adjunction is the
composite closed-support adjunction with its kernel inclusion normalization, uniquely
determined by the epic constant-coefficient quotient. The ordinary tensor factorization
is natural, its signed complex extension is the existing totalization comparison, and
its derived extension follows from the two-variable localization universal property
using functorial flat resolutions.

The earlier compile timeout came from repeated monoidal instance expansion at
`pullback f g`. Generic comparison interfaces and wrappers at a variable scheme keep
those structures shared. The signed-total `eqToHom` localization factor is retained.
The complete module compiled in 53.7 seconds in the final import-order check.
The unchanged consumers `SupportedProductLocalization`, `SupportedExteriorClassArrows`,
and `ProEtaleSupportedExteriorProduct` also compile against the rebuilt module. Seven additional imports are proof-only; all six original public imports
are unchanged. No source-library module is modified.

Definition changes are recorded in:

- `coord/changes/X3-supportedCoefficientTensorComplexHom.md`
- `coord/changes/X3-supportedCoefficientTensorComplexCondition.md`
- `coord/changes/X3-supportedCoefficientTensorComplex.md`
- `coord/changes/X3-supportedCoefficientTensorDerivedHom.md`
- `coord/changes/X3-supportedCoefficientTensorDerivedCondition.md`
- `coord/changes/X3-supportedCoefficientTensorDerived.md`

## Proved and sorry left

Closed seven of seven original holes, all attached to
`def-pur-supported-exterior-product`:

- `AlgebraicGeometry.Etale.supportedComplexTensorGeneric_eq`
- `AlgebraicGeometry.Etale.supportedCoefficients_exact`
- `AlgebraicGeometry.Etale.exists_unique_supportedCoefficientAdjunction`
- `AlgebraicGeometry.Etale.supportedProductImmersion_isClosedImmersion`
- `AlgebraicGeometry.Etale.exists_unique_supportedCoefficientTensor`
- `AlgebraicGeometry.Etale.exists_unique_supportedCoefficientTensorComplex`
- `AlgebraicGeometry.Etale.exists_unique_supportedCoefficientTensorDerived`

There are zero remaining sorry declarations in the item, zero added holes, and zero
split-off results. Every added helper is proved. This is a proof delivery rather than
a decomposition; existing source-library dependencies are reused as allowed by stage 3.

## No longer needed

No original import is removed and no library module is withdrawn. The proof does not
use the separate independent-coefficient statements
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, or
`Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`: the existing ordinary module-sheaf
monoidal and flat-resolution APIs already supply the constructions in this item.
The ordinary quotient and exactness proofs also avoid a separate finite-stalk formula
or constant-stalk computation. These are unused proof routes here, not requests to
withdraw their nodes or adopted source declarations; dependencies used elsewhere remain.

## Where the brief, the DAG or earlier work was wrong

The retained report claimed an adjunction proof while still listing its sorry; both
remaining holes are now actually closed. The retained coefficient-quotient epi proof
also omitted the adjunction unit; the repaired proof establishes that unit is epic
using its cokernel before composing with the constant-sheaf isomorphism.

The compile limit was an interface problem, not missing mathematics. Specializing
large tensor constructions directly at a fibre-product scheme repeatedly expanded
instance arguments. Sharing the generic and variable-scheme interfaces makes the
complete construction compile below the unchanged limit. No theorem statement or
mathematical normalization is weakened, and no unit statement or prescribed step is
bypassed. There are no new DAG nodes or forced adaptations.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
