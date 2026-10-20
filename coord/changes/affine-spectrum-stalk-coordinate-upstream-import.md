# Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData

## Reason

Restore the quarantined module after the upstream sync to `5f7b33eac`. Its old public
import loads the local copy of the single-complex stalk condition and its tensor model,
whereas its proof import `WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport`
loads the upstream copies. Compiling the original quarantined file reproduces:

```text
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel failed,
environment already contains 'ModuleCat.BaseDerivedTensorCohomologyModel._sizeOf_inst'
from Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

Use the upstream stalk-condition module consistently. This is an import compatibility
repair with zero original holes. No declaration, proof, signature, visibility, instance,
definition body or target statement is changed. The original ring and complex coordinates
use the same canonical constructions; no target meaning changes or semantic re-review
is required. The source-library files are not edited.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
```

All text outside the first public import is byte-for-byte identical to the quarantined
module, including every declaration and the complete existing proof.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData
--allow-missing --uses exists_affineSpectrum_stalk_coordinate_data` reports zero active
importers and zero active declaration users, because the item and its direct importer
are quarantined. Searching both `lean/` and `quarantine/` finds exactly one direct caller,
listed below. It already publicly imports the upstream `IsoPullbackStalkCohomology`,
which imports the same upstream stalk condition through `StalkComparisonSourceTransport`.
It therefore requires no adaptation. Its unchanged quarantined source compiled cleanly
against the repaired module in a temporary sandbox validation. Only the assigned item
is restored in this delivery; the caller's validation copy is excluded from the packet.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData | G9 | Restore with the upstream public import; unchanged theorem and proof compile. |
| Sheaf.AlgebraicGeometry.AffineSpectrumTensorCoordinateData | unclaimed | Quarantined direct caller; unchanged source compiles against this repair. |

## Return repair and validation

The latest return at branch head `e332a34a86` reports that the item path changed after
its delivery base `e0d550965`. Read that return and the current rework and claim records.
The active library path remains absent; its current source is preserved at the rework
archive named above. Rebuilt the sandbox module from that current source and reapplied
the import replacement. An exact comparison confirms that this public import is the
only changed line, preserving all current declarations and proofs. The normal delivery
tool prepares the replacement packet on its current fetched `sheaf-dag` base.

Fresh remote single-file checks reproduce the original duplicate-import failure
(0.8 seconds). An ordered compile of the repaired module, an axiom probe, and the current
unchanged direct consumer succeeds without errors or warnings (0.1 seconds each).
The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
Validation copies reside only under `scratchpad/` and are excluded from the packet.
`downstream.py --allow-missing --uses` still reports zero active importers and users;
the only quarantined direct caller remains unclaimed. The upstream import passes the
import-direction check. No new node or proof hole is added.

## Status

landed 20261020T145515-L-2404415 2026-10-20 (merge of deliver/G9/Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData)
