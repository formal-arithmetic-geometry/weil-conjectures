## What changed

The signature of CategoryTheory.Functor.normalized_bottom_unit_formula is unchanged.
Its proof factors the concrete bottom comparison into the double-truncation portion,
the specified shifted single-object comparison, and the inverse homology of the lower
truncation projection. It then applies canonical-cycle transport, normalizes the actual
single-object unit, and cancels the lower-truncation homology map under S.

Added DerivedBottomCycleTransport, containing the explicit initial portion of the
comparison and its cycle-transport statement. Added DerivedSingleShiftNormalization,
containing explicit integer-degree single-unit maps and the shifted comparison.
Its normalization theorem is fully proved. Private helpers generalize the already
proved SingleQuotientInverseShift, MappedSingleInverseShift, and
RightDerivedSingleUnitShiftTransport calculations from natural numbers to integers.
The fully proved SingleHomologyShiftComparison and
RightDerivedSingleUnitHomologyComparison finish the calculation. No existing
module other than the assigned item is modified; no definitions choose data from
an unproved theorem.

## Proved and sorry left

Closed the original hole in CategoryTheory.Functor.normalized_bottom_unit_formula,
node new-lem-pc-derived-bottom-unit-normalization-formula, by a proved combination
of intermediate statements.

Also fully proved CategoryTheory.Functor.rightDerivedPlusSingleUnitHomologyAt_comp_shiftIso,
node new-lem-pc-derived-single-shift-normalization. Its four private helper theorems
are proved, and every definition is an explicit construction.

Added one remaining hole: CategoryTheory.Functor.rightDerivedBottom_cycle_transport,
node new-lem-pc-derived-bottom-cycle-transport. This stops at homology of the actual
unit on the single cohomology object; it contains neither the shifted single-object
comparison nor its classical degree-zero cancellation. Its hypotheses and conclusion
are stated in DerivedBottomCycleTransport and its complete intended proof is in the
docstring and DAG node.

This is a decomposition: one original hole closed, one strictly intermediate hole
added, with the single-object normalization proved. It does not claim a net decrease
in the number of holes or that the target is now independent of sorry.

## No longer needed

Removed the direct proof import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison
from the assigned module. That proved theorem is still used by
DerivedSingleShiftNormalization, so its node is not pruned from the total closure.
The new single module imports PlusSingle, rather than the stronger PlusCompatibility;
it requires enough injectives but no K-injective-resolution assumption.

No original DAG dependency is entirely unused: the explicit comparison remains a
statement dependency; the degree-zero unit theorem is used through the proved shifted
normalization; bounded-below/unbounded compatibility is used in the initial comparison.
No module is claimed pruned from the targets' total import closure.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan did not distinguish the double-truncation cycle transport
from the shifted single-unit calculation. The library already proves the latter's
constituent quotient, mapped-single and unit-shift calculations, but three of those
interfaces restrict their degree to Nat. Their existing proofs do not use nonnegativity:
the private integer generalizations compile. The source single-homology shift theorem
already takes an arbitrary integer and is reused without adaptation.

The local compiled snapshot initially lacked DerivedBottomComparison after its recent
landing. Work continued on independent modules until the next published build supplied
it; no dependency was restated or compiled outside the prescribed workflow.

The new statements include n=0, negative n, zero objects and the zero functor. The
cycle-transport equation is a naturality calculation with specified maps, so changing
the comparison by an arbitrary sign is not permitted. Stacks Tags 05TC (2) and 05TD (3)
were read for the truncation and degree-zero arguments; the canonical equations are
agent-written elaborations of those arguments and the named library constructions.
The blueprint unit record sk-thm-picard-semicon has empty realized statement and step
lists; this change operates below the unit level and preserves the parent's route.

## New nodes

new-lem-pc-derived-single-shift-normalization records the fully proved normalization
of the actual derived unit on a single object in any integer degree. It uses the
existing single-homology shift comparison and degree-zero unit comparison. Its new
module is lean/Sheaf/CategoryTheory/Abelian/DerivedSingleShiftNormalization.lean.

new-lem-pc-derived-bottom-cycle-transport records the remaining canonical-cycle
transport through the initial portion of the specified double-truncation comparison,
ending at the actual unit on the single cohomology object. Its new module is
lean/Sheaf/CategoryTheory/Abelian/DerivedBottomCycleTransport.lean.

The assigned node's proof and proof_deps now describe the compiled combination.
No statement, definition, or visibility of an existing declaration changes, so there
are no change records or forced adaptations.

## Second reading by F1

1. I compared the delivered assigned module with the repository version. The
   `normalized_bottom_unit_formula` signature is byte-for-byte unchanged; only its
   imports and proof body changed. The two added modules contain new declarations
   only, and no existing module outside this delivery is modified.

2. I compiled all three modules with `lcompile.py --all`. Compilation succeeds.
   The only remaining `sorry` is the named public theorem
   `CategoryTheory.Functor.rightDerivedBottom_cycle_transport`; it has a complete
   source-based proof plan in its docstring and a matching split node. There are no
   axioms, unsafe declarations, hollow definitions, or forbidden implementation
   features. The proved normalization theorem uses only the permitted foundational
   axioms apart from the explicitly open transport theorem in its import closure.

3. I checked the new statements against their definitions and edge cases described
   in the report: arbitrary integer degrees (including zero and negative degrees),
   zero objects, and zero functors. The shifted normalization is fully proved and
   the cycle transport is strictly an intermediate reduction ending at the actual
   single-object unit; it does not restate the assigned target. Searches recorded in
   both new nodes found no existing declaration with either statement.

4. The proof follows the planned route: explicit double truncation, canonical-cycle
   transport, integer single-object shift normalization, and cancellation of the
   lower-truncation homology isomorphism. The assigned module no longer imports the
   direct single-unit comparison. The new modules retain the imports needed by their
   public statements and proofs; no original proof dependency is unused. The unit
   route remains below the Picard-semicon unit and its realized record is unchanged.

5. The DAG proof, proof dependencies, proof origins, declarations, and report agree
   with the Lean code. The assigned target closes its original hole; one strictly
   simpler transport hole is split off and documented. No statement or definition
   was changed, and no change record is required.

I changed only this report section after the first delivery check; no Lean source or
DAG content was altered during second reading.
