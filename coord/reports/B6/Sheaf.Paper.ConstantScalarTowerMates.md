## What changed

Filled both proof holes in Sheaf.Paper.ConstantScalarTowerMates. The ordinary comparison
is the pointwise lift of the existing general ring-sheaf comparison, and uniqueness follows
from the prescribed identity on sections. Exact tensor makes its right adjoint, restriction,
preserve K-injective tower complexes. The existing proved square_exists and square_unique
helpers in CategoryTheory.ExactDerivedSquare then provide the derived comparison with exactly
the existing whole-cochain unit normalization. Those private proof helpers are reused through
one private `import all Sheaf.CategoryTheory.DerivedExactSquareCoherence`.
A proved private generic helper converts the upstream unit formula into unitCompatible
before specialization to tower categories. This avoids expensive kernel conversion across
the concrete sheaf constructions: the full module compiled in 14.1 seconds after this
refactoring, compared with a 60-second timeout when performing that conversion directly
in the tower proof. Removed the temporary profiling option before delivery.

All existing declaration signatures, definition bodies, public imports, attributes and
normalizations are preserved. Updated the item's DAG proof and dependencies to record this
route. No consumer adaptations or change records are needed.

## Proved and sorry left

Closed both existing holes:
- WeilConjectures.PurStrictScalar.properRestrictionOrdinary_existsUnique.
- WeilConjectures.PurStrictScalar.properRestriction_existsUnique.

Zero sorry left in the item; zero holes added or split off. The proof uses the existing
WeilConjectures.PurStrictScalar.tensor_exact theorem, whose proof remains a separate item.

## No longer needed

None. The original DAG had no proof steps or proof dependencies to prune. The original public
import supplies the unchanged definitions and remains necessary. The only added import
supplies the two proved derived-square helpers used by the proof. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item's DAG supplied no proof steps. Its docstrings do give the needed argument, which
is now realized using existing ordinary sectionwise and derived unit-normalization APIs.
No mathematical statement or definition repair was needed. The unit route is preserved.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
