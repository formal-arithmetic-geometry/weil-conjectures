## What changed

Proved seven of the nine original holes in `Sheaf.Paper.FiniteCoefficientPoint`.
The size lift is fully faithful by the classification of derived field-complex maps
by graded cohomology; its essential surjectivity uses a zero-differential model and
shrinks its finite-dimensional terms. Exact sections and the existing finiteness
specification give all three target predicates. The integral scalar action descends
from its termwise action. The rational functor is constructed on Hom tensors, and
the coefficient-down and tensor/lift comparisons are explicit linear isomorphisms.

Every original public declaration, signature, definition body, and public import is
preserved. Added helpers are private and proved; added imports are private. Local
irreducibility controls unfolding of the size-descent construction. The private
coefficient-complex import requires disabling its duplicate derived-category
instance, matching the instance choice used by PointSectionsScalarExtension.

## Proved and sorry left

Baseline: nine holes. Closed seven:

- `WeilConjectures.pointFibreModuleLift_mem`
- `WeilConjectures.pointFibreSizeLift_equivalence`
- `WeilConjectures.pointFibre_sections_mem`
- `WeilConjectures.pointIntegralFibre_linear`
- `WeilConjectures.pointRationalFibre_existsUnique`
- `WeilConjectures.pointFibreRationalDown_existsUnique`
- `WeilConjectures.pointFibreTensorLift_existsUnique`

Two original holes remain, both attached to `def-weil-finite-coefficient-point`:
`WeilConjectures.pointRationalFibreScalar_existsUnique` and
`WeilConjectures.pointQbarFibre_existsUnique`. No holes are added or split off.
The delivered module compiled successfully through lcompile.py in 48.8 seconds,
with exit code 0 and no warnings. All 53 original public declaration signatures
match the current repository source; there are exactly two remaining sorry tokens.

## No longer needed

No original import, declaration, node or module is withdrawn. The original node
had no proof steps or proof dependencies to prune. The proof uses the already
proved field-complex splitting theorem instead of developing new derived
universe-change machinery. Private proof imports added: FieldComplexCohomologySplitting, Finiteness.Small,
Algebra.Module.Shrink, ProEtaleBoundedConstructibleTriangulated, and the private APIs
of ScalarLocalizationTriangulated, IntegralScalarExtensionWellDefined,
PointSectionsScalarExtension and CoefficientComplexRationalization. Each supports
a retained proof. Trial localization and common-stage descent helpers are omitted.

## Where the brief, the DAG or earlier work was wrong

The node's blueprint_update changes the semantics to condensed coefficients and
an ordinary derived category over Qbar. The assigned public Lean interface is the
previous four-stage interface and has existing consumers. This proof packet
preserves that interface. Migrating it to the newer blueprint requires a separate
semantic reconciliation; none of the target statements or coefficient definitions
is changed here.

The outstanding Qbar construction additionally needs compatibility of the
intrinsic sf scalar associator with the associator used by the sections API, and
compatibility of the size and coefficient transports with tensor towers. Trial
proofs and the ordinary sheaf-model tower calculation remain in the scratchpad.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
