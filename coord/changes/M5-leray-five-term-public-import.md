# Sheaf.CategoryTheory.LerayFiveTerm public statement imports

## Reason

The upstream sync quarantined this module. For the 2026-10-20 14:12 UTC stale-base return of delivery head
`5950675cff` (old base `6488bba00`), the module was reconstructed from the
current quarantined source with the five proved theorem bodies and visibility
repair reapplied. All nine public signatures and all four complete
definitions were compared byte-for-byte and are unchanged. Its first public
definition fails
with `Unknown identifier BigradedExactCouple`; the compiler explains that the
name is imported privately. Public signatures also use `LimitSubobjects`,
`AlphaColimit`, `ConvergesTo`, and the PBC image filtration. Publicly importing
the existing convergence module makes these existing types available. No
statement, definition body, instance, universe, or attribute changes.

## Old

```lean
public import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.Filtration
import WeilConjectures.Algebra.Homology.ExactCouple.Basic
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.PBCFiltration
```

## New

```lean
public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
```

The private Subobject.Limits import supplies only the new proofs.
The redundant private Mathlib.CategoryTheory.Abelian.Exact import from the
returned packet is removed; ExactCouple already provides that API publicly. The convergence module
already publicly imports the exact-couple and PBC filtration modules.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.LerayFiveTerm` | M5 | Restored; visibility repaired; all five holes proved. |
| `Sheaf.AlgebraicGeometry.LerayLowDegree` | quarantined | Sole direct consumer found in the quarantined sources; its existing use of `lerayFiveTerm` keeps the identical signature and canonical maps. No adaptation needed. |

The active library has no importer because this module and its consumers were
quarantined. No target definition or statement changes; target statement
review is not reopened by this import visibility correction.

## Status

landed 20261020T145528-L-2407490 2026-10-20 (merge of deliver/M5/Sheaf.CategoryTheory.LerayFiveTerm)
