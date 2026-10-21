## What changed

Filled the six proof bodies in `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification`.
Exactness follows from `sheafRingCoefficientOrdinaryAdjunction`; Mathlib supplies preservation
of quasi-isomorphisms and compatibility of the localization comparison with shifts.

Private helpers construct restriction/sheafification comparisons and the sectionwise tensor
swap, then prove naturality and the pure-tensor normalization. The existing scalar-first
complex serves as the S-linear presentation, with its B-linear identification with the actual
scalar-last tensor obtained from this swap. The K-flat counit and the inverse resolution map
give the prescribed computation comparison; eta and delta are the stated composites.

For an arbitrary A-linear coefficient map, restrict it to B, tensor with the identity,
and sheafify. Conjugating this map by the supplied S-linear and T-linear swaps constructs the
map on the scalar-last presentations. The pure-tensor equation and localized conjugation
identity follow from the normalization and cancellation. No ring-homomorphism condition on
the coefficient map is used. No existing declaration signature, definition or public import
changes. The static interface check classifies the added proof-support commands as
an interface change; `coord/changes/restricted-kflat-tensor-proof-support.md` documents
the commands and the unchanged consumer held by X5. The proof follows the seven existing DAG steps; no new statements are split off.

## Proved and sorry left

Closed all six original holes (node `lem-pe-restricted-kflat-tensor-identification`):

- `SheafOfModules.restrictedTensorScalars_preservesFiniteLimits`
- `SheafOfModules.restrictedTensorScalars_preservesFiniteColimits`
- `SheafOfModules.restrictedTensorScalars_quasiIso`
- `SheafOfModules.restrictedTensorLocalization_commShift`
- `SheafOfModules.nonempty_restrictedKFlatTensorIdentification`
- `SheafOfModules.restrictedKFlatTensorIdentification_coefficientMap`

Holes added: zero. Holes left in this module: zero. Split off: zero.

## No longer needed

None. All existing imports and all stated proof dependencies are retained. There is no
withdrawal or change to the unit route.

## Where the brief, the DAG or earlier work was wrong

No statement error found. Private sheafification comparisons are abstract in the weak
sheafification instance, avoiding repeated unfolding of its construction from strong
sheafification. Comparing the forgotten isomorphism directly with the identity makes its
inverse formula cheap to check. Explicit module objects and pure-tensor equations prevent ambiguous scalar
structures from causing expensive elaboration. The pure-tensor and coefficient constructions work
without flatness of the ring maps, including zero rings and modules and the zero coefficient map.
The flat-term hypothesis is retained verbatim; the given derived model already supplies
its computation isomorphism for every K-flat complex.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
