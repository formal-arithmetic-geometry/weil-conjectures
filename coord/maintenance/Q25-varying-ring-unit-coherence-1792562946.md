# Q25 varying-ring pullback unit-coherence maintenance

The stage-2 repair of lem-sp-varying-ring-pullback-unit-coherence was blocked by
an unnecessarily broad dependency closure and then by the stage-2 delivery gate.
The gate requires even unchanged existing proofs in a supplied dependency module
to be sorry. Replacing the published proofs would discard verified work.

This maintenance applies only the worker's independently checked import repairs:

- SemilinearSystemsExistence: remove the unused RingedInternalHomShiftOfUniverses
  import, which reached the unrelated failing RingedSiteDualityMaps proofs.
- VaryingRingOperations: import the owning StrictTowerOpenExtension module instead
  of the broad StrictTowerProperOpenCalculus, and explicitly import
  Ring.FilteredColimits and ConcreteCoefficients for ring sheafification.

Every non-import line of both modules is byte-for-byte unchanged. No declaration,
signature, proof, docstring, coefficient hypothesis, or DAG record is changed.
The narrowed public import removes an unnecessary transitive re-export; downstream
modules that need the larger proper/open calculus should import it explicitly.

The worker should omit these now-landed dependency modules and their node copies
from its packet and retain its original unit-coherence statement. The protected
preflight and landing tools were not changed. The gate's lack of comparison with
unchanged dependency declarations remains an upstream tool issue documented in
the maintenance REPORT.md on the launcher host.

Validation (sequential tools/lean_file.sh; the project's unchanged 60 s limit):

- `lean/Sheaf/Paper/SemilinearSystemsExistence.lean`: Compiled in 6.1 s.

- `lean/Sheaf/AlgebraicGeometry/VaryingRingOperations.lean`: Compiled in 33.0 s.

Backups: each edited source has the suffix `.maint-Q25-unit-coherence-1792562946.bak`.
