## What changed

Repair of the returned delivery `935fb735823`, reviewed by C-935fb. Reconciled the
node with current sheaf-dag metadata and included the corrected change record
directly in the packet. The landing failure concerned the reviewer override name:
change-record overrides require `.change.md`, while the returned attempt supplied
the ordinary `.md` basename. The record now documents that distinction and the
required renewed target-interpretation review. The two reviewed proof bodies and
all original theorem statements are retained. Applied the reviewer’s actual record
corrections: added the missing direct consumer
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels` and corrected the recorded
holder of `CompactSupportScalarProjectionIdentification` from U6 to K7 (as checked
by C-935fb).

Proved ordinary scalar/tensor naturality by transposing through the normalized scalar
adjunction and testing on pure tensors. Proved the completed-to-ramified reduction
square by quotient-ring extensionality and the specified finite projection normalization.
The positive-index arithmetic includes the boundary n = 1 and arbitrary positive
e, and the impossible n = 0 case is discharged explicitly.

Added private proved tensor helpers and four public proved canonical site-instance
aliases. Added explicit existing result types and canonical
preadditivity instances to keep the full file within the compile limit. See
coord/changes/f8-integral-compact-support-scalar-tensor-elaboration.md.

## Proved and sorry left

Closed 2 of the original 18 holes; added 0 holes; split off 0 statements.

Proved:

- `WeilConjectures.PurCompactSupport.scalarOrdinaryTensor_naturality`.
- `WeilConjectures.PurCompactSupport.ramified_reduction_square`.

The following original holes remain, all attached to
`lem-pur-compact-support-integral-coefficient-comparison`:

- `WeilConjectures.PurCompactSupport.comparison_commShift`.
- `WeilConjectures.PurCompactSupport.comparison_composition`.
- `WeilConjectures.PurCompactSupport.comparison_identity`.
- `WeilConjectures.PurCompactSupport.scalarOrdinaryTensor_existsUnique`.
- `WeilConjectures.PurCompactSupport.scalarTensor_existsUnique`.
- `WeilConjectures.PurCompactSupport.openComparison_isIso`.
- `WeilConjectures.PurCompactSupport.finiteComparison_isIso`.
- `WeilConjectures.PurCompactSupport.integralCoefficientComparison`.
- `WeilConjectures.PurCompactSupport.recordedIdentification_existsUnique`.
- `WeilConjectures.PurCompactSupport.reductionComparison_isIso`.
- `WeilConjectures.PurCompactSupport.refinementProperOpen_existsUnique`.
- `WeilConjectures.PurCompactSupport.comparison_refinement`.
- `WeilConjectures.PurCompactSupport.refinementComparison_coherence`.
- `WeilConjectures.PurCompactSupport.comparison_strict_towers`.
- `WeilConjectures.PurCompactSupport.comparison_projection`.
- `WeilConjectures.PurCompactSupport.projectionDomain_complete`.

## No longer needed

None withdrawn. Two private proof imports were added: ScalarHomOrdinaryTensorComparison
and AdicCoefficientDatum. No original imports were removed. The two completed subarguments
use the coefficient and tensor APIs already below the item. The seven stated plan
dependencies remain relevant to the other unfinished comparison assertions.

## Where the brief, the DAG or earlier work was wrong

The seven advertised lower proof-dependency modules transitively import this item.
For example, import_direction.py rejects importing CompactSupportCoefficientModels
back into this module. A genuine shared-interface extraction was explored in the
scratchpad, with the existing names and signatures, to break that cycle. It is not
part of this partial packet. No downstream declaration was deleted or weakened.

The unchanged original full module also exceeded 60 seconds in profiling attempts.
Explicit result types and canonical instances repaired elaboration for this packet;
no timeout was increased and no source-library file was changed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
