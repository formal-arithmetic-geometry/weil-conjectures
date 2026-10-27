## What changed

Fill the geometric base-change instances and assemble the coefficient, tensor,
scalar-extension and operation-domain bridges from the published normalized APIs.
No declaration signature or definition body changes.

## Proved and sorry left

The original module has eleven holes. Ten are closed:
`sfProjectionWeilMap_isSeparated`, `sfProjectionWeilMap_locallyOfFiniteType`,
`sfProjectionWeilMap_quasiCompact`, `sfProjectionWeilCoefficientBridge`,
`sfProjectionWeilIntegralTensorDomains`, `sfProjectionWeilIntegralTensorBridge`,
`sfProjectionWeilCommonTensorBridge`,
`sfProjectionWeilScalarDomainBridge`, `sfProjectionWeilTensorDomainBridge`, and
`sfProjectionWeilCommonDomainBridge`.

One original hole remains: `sfProjectionWeilRationalTensorBridge`. The integral-to-ambient
rational tensor functor equality was developed, but the full Frobenius transport
argument has not passed the per-file elaboration check. No declaration is renamed
or weakened. The delivered candidate compiled successfully through lcompile.py (58.1 seconds).
Holes closed: 10. Holes added: 0. One original hole remains; no statements are split off. All declarations realize
`lem-sf-projection-weil-tensor-domain-bridge`.

## No longer needed

Removed proof imports `Sheaf.Paper.RationalLatticeAdicDomain`,
`Sheaf.Paper.IntegralOperationsPreserveConstructible`, and
`Sheaf.Paper.SfIntegralCompactSupportConstructible`. The coefficient bridge uses
the detailed coefficient comparison and stratified-perfect characterization directly;
the operation-domain witnesses come from the datum normalizations.

Direct proof dependencies no longer needed here: `lem-pur-rational-lattice-adic-domain`,
`lem-wf-constructible-tensor-koszul-unit`,
`lem-pur-integral-operations-preserve-constructible`,
`lem-sf-integral-compact-support-constructible`, `def-weil-rationalization-karoubi`,
and `lem-fix-weil-operations`. The normalized tensor comparison already encapsulates
the Koszul argument; localization APIs are imported by the tensor module. The Weil
operations theorem is a consumer of this bridge rather than a premise. No module is
withdrawn, and dependencies still used by the normalized constructions remain needed.

## Where the brief, the DAG or earlier work was wrong

The operation datum already records the restricted integral pullback, tensor and
compact-support functors and their object normalizations. Consequently its output
objects supply constructible witnesses directly; the preservation results are used
inside those recorded constructions rather than reapplied to reconstruct outputs.
At common coefficients, the compositum tensor comparison and the stage-system unit
identify the given stage with the common-stage tensor. No integral lift of a
rational Weil structure is used.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
