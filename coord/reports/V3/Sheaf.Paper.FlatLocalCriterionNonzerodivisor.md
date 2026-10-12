## What changed

Proved `RingTheory.flat_of_localCriterion_nonzerodivisor` directly from the existing upstream
local flatness criterion. The proof constructs the principal-ideal linear equivalence,
tensors it, proves injectivity using regularity on M, transports quotient flatness across
an A/(x)-linear equivalence, and checks Jacobson containment for the local homomorphism.

Removed the proposed module `Sheaf.Paper.FlatLocalCriterionNonzerodivisorData` and its new
node: all its verifications are now proved inside the target proof. No new declaration,
definition or statement is delivered. The existing theorem signature is byte-for-byte
identical to the repository version. The existing docstring is unchanged.

Made the filtration import private and exposed its signature dependencies explicitly.
The import change record is
`coord/changes/flat-local-criterion-nonzerodivisor-imports.md`.
The sole direct importer, `Sheaf.RingTheory.FlatOverRegular`, is checked unchanged against
the newly compiled target. The node's proof steps now describe the actual Lean argument.

## Proved and sorry left

Closed: `RingTheory.flat_of_localCriterion_nonzerodivisor`
(node `lem-weil-pbc-flat-local-criterion-nonzerodivisor`).
Added: none. Sorry left in the delivered module: none.
The proposed hole `RingTheory.flat_localCriterion_nonzerodivisor_data` was fully discharged
and its module and node removed rather than delivering an unnecessary intermediate theorem.
This is one original hole closed, zero holes added; not a decomposition.

## No longer needed

Neither original proof dependency is pruned: the proof uses
`lem-weil-pbc-flat-variant-local-criterion`, realized by
`Module.Flat.of_flat_quotient_of_lTensor_injective`, and quotient-flatness
`def-weil-pbc-flat-ring-map`. Both original Lean imports are retained; the filtration import
is now plain because only its proof theorem is used. No existing module is pruned.
The proposed new data module and its proposed node are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's one-hole decomposition did not establish net progress. Its new theorem
also lacked the required full proof in words and its node copied historical review metadata
from the parent. These issues disappear with removal of that theorem and node.
The principal-ideal and quotient verifications can all be proved using existing Mathlib
infrastructure within this session. No mathematical statement of the original DAG is wrong.

## Second reading by V3

1. PASS: diffed the delivered module against the read-only repository. The complete existing
   theorem signature and docstring are byte-for-byte unchanged. No definitions changed.
   The only interface change is the documented import visibility correction.
2. PASS: compiled the final module locally using lcompile.py, without errors or warnings.
   No sorry, axiom, unsafe, opaque, implemented_by or extern occurs in the delivered code.
   A scratch copy with `#print axioms RingTheory.flat_of_localCriterion_nonzerodivisor`
   is compiled to verify exactly the three permitted axioms. No data is chosen from an
   unproved theorem: the ideal map is explicit and its equivalence uses proved bijectivity.
3. PASS after repair: there are no split-off statements to deliver. Repeated independent
   Loogle and LeanFinder searches and repository/Mathlib rg searches found tensor maps,
   quotient equivalences and the upstream general criterion. Used these existing facts.
   The intermediate verifications hold also for the zero module; a field supplies no
   element satisfying both original maximal-ideal membership and regularity. The principal
   ideal equivalence uses precisely regularity on A, and tensor injectivity uses regularity
   on M. No hypothesis was altered to make these arguments work.
4. PASS: the proof follows the original two-step route (principal-ideal tensor injectivity,
   then the general local criterion), with explicit Jacobson and quotient checks. It uses
   the recorded upstream criterion and preserves the unit route in dag/units/sk-thm-p1.json;
   no unit statement or realized step is bypassed. Public imports supply only signature
   dependencies; local homomorphism proof lemmas and filtration are plain imports.
   No original proof_deps or existing module becomes unnecessary. The new helper is removed.
5. PASS after repair: updated proof and proof_origin of the existing node; proof_deps is
   the union of the recorded uses and stays the same as the original node. The Lean record,
   natural-language statement, statement dependencies and unit are unchanged. No new nodes.

Changes by the second reader: proved all proposed lower verifications, folded the proof into
its target, removed the extra holed theorem/module/node, corrected import visibility with
its change record, updated the DAG proof, and rewrote the report to reflect one net hole
closed. The unchanged direct importer is compiled against the delivery overlay.
