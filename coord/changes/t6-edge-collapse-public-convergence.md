# CategoryTheory.BigradedExactCouple.edge_collapse

## Reason

Restore the quarantined module at its original path after sync 5f7b33eac.
The original file fails because its public theorem signature uses convergence
objects imported privately. The compiler explicitly requests a public import of
WeilConjectures.CategoryTheory.ExactCoupleConvergence. Make that import public;
its public dependency chain supplies ExactCouple and PBCFiltration.
Remove the remaining redundant private imports. The theorem signature, docstring,
and proof body are byte-for-byte identical to the current quarantined text.

Returned-delivery repair: the previous packet ba738af137 failed to land after
an intervening write following d92f73d8e. On this retry the original module is
absent at its lean/ path in both the shared checkout and server working tree.
Reconstructed the packet from the current quarantine file and reapplied the
import fix. The original again fails with lean.invalidField and explicitly
requests this public import; the repaired module compiles cleanly in 1.7 seconds.
No declaration text below the imports or node metadata changed.

## Old

```lean
public import Sheaf.CategoryTheory.ExactCouple
public import Sheaf.CategoryTheory.Filtration
import WeilConjectures.Algebra.Homology.ExactCouple.Basic
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.PBCFiltration
```

## New

```lean
public import Sheaf.CategoryTheory.ExactCouple
public import Sheaf.CategoryTheory.Filtration
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
```

Only the import header changes. In particular, LimitSubobjects, AlphaColimit,
ConvergesTo, cycleBoundaryTower, pageInfinity, and toPageInfinity remain the
existing source-library declarations; no definitions are replaced or duplicated.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.EdgeCollapse | T6 | Restored and compiling with its unchanged signature. |

No current Lean module imports Sheaf.CategoryTheory.EdgeCollapse or mentions
CategoryTheory.BigradedExactCouple.edge_collapse (searched both library roots).
The quarantined tree likewise has no importer. No consumer needs adaptation.
The import-direction check allows the public convergence import.
No source-library file, target statement, definition, or DAG proof route changes.

## Status

landed 20261020T145539-L-2410071 2026-10-20 (merge of deliver/T6/Sheaf.CategoryTheory.EdgeCollapse)
