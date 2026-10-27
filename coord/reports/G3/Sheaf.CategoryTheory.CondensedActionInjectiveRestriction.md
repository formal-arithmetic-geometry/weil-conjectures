## What changed

Restored lean/Sheaf/CategoryTheory/CondensedActionInjectiveRestriction.lean from
its current quarantine archive. Removed its unused public import of
Sheaf.CategoryTheory.CondensedProductActionInflation, eliminating the source
path into the quarantined CompletionUnitFiniteMateComparison closure.
Every declaration, proof, docstring, and other import is preserved verbatim.
The existing CondensedDerivedInvariants import supplies the structures and
instances actually used by the proofs. The repaired item compiles in 35.7 s. Its source import closure has 320
project modules and no missing source. Both archived direct consumers were
compiled against it. FreeParameterDegreeZeroData passed alone in 27.4 s.
The original product-bar consumer first exceeded the limit at 62 s; a
subsequent profiling compile passed (exit 0), with 12 s cumulative kernel
checking, 6.64 s instance inference, and 8.78 s linting. The profiling options
produced only their expected development-option warnings. Neither unchanged
consumer nor those debugging options is included in this delivery.

Change record: coord/changes/G3-condensed-action-injective-restriction-import.md.

## Proved and sorry left

This is the assigned quarantine/import repair, not a new mathematical proof.
Closed 0 holes; added 0 holes; 1 original hole remains:
Profinite.CondensedAction.restriction_free_flat_comparison
(lem-sfb-condensed-action-injective-restriction).

The existing proofs of Profinite.CondensedAction.forget_tensor_induction,
Profinite.CondensedAction.product_tensor_induction, and
Profinite.CondensedAction.action_injective_restriction are preserved.
There is no new theorem, new node, or hollow definition.

## No longer needed

Removed the unused public import
Sheaf.CategoryTheory.CondensedProductActionInflation. The proof uses
CondensedDerivedRestriction.forgetExact and restrictionLimits from the retained
CondensedDerivedInvariants module, and ProductForgetting.exists_datum from the
retained ProductActionExactForgetting module. No declaration of the removed
import is referenced. All other imports are retained to preserve the archived
public interface. No DAG node or module is withdrawn: other parents can still
need the removed import's node, and the existing item's Lean attachment and
all statement and proof dependencies remain intact.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it is quarantined, not because its
mathematics was withdrawn. Its rework row identifies the transitive dependency
on CompletionUnitFiniteMateComparison. The archived direct import of
CondensedProductActionInflation is redundant; dropping it suffices to compile
the original declarations and existing proofs without that missing source.
The remaining comparison theorem is still an open mathematical task. No
statement is weakened, and no proof route or unit realization is changed.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
