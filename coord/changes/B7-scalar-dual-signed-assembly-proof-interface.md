# CategoryTheory.scalarDual_signed_assembly

## Reason

Remove the unused public import `Sheaf.CategoryTheory.SiteCoveringAxioms`.
The scalar-dual comparison uses arbitrary Grothendieck topologies and does not use
the covering-presieve axiom predicate exported by that module. The proof uses
Mathlib's single-target cochain equivalence through a private proof import.
A theorem-local heartbeat setting supports elaborating the six-clause proof.
The theorem signature, existing definitions and mathematical meanings are unchanged.
The static checker treats public-import removal and the local option as interface changes.

## Old

```lean
public import Sheaf.CategoryTheory.SiteCoveringAxioms
```

The theorem previously had no local heartbeat setting and its proof was `by sorry`.

## New

The unused public import above is removed. The new proof-only import is:

```lean
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
```

The existing theorem is proved, with this setting scoped to its declaration:

```lean
set_option maxHeartbeats 600000 in
```

All new helpers are private and fully proved. The compilation wall-clock limit is unchanged.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.ScalarDualSignedAssembly --uses
CategoryTheory.scalarDual_signed_assembly` reports zero downstream modules and
only the item's own occurrence of the declaration name. No consumer needs adaptation.
Parents citing the existing DAG node retain its original statement and proof route.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ScalarDualSignedAssembly | B7 | Complete proof; unchanged signature. |

## Status

landed 20261023T090657-L-684806 2026-10-23 (merge of deliver/B7/Sheaf.Algebra.Homology.ScalarDualSignedAssembly)
