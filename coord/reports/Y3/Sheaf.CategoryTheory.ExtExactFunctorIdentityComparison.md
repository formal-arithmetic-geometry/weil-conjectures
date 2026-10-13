## What changed

Repaired `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison` by restoring the
private `CategoryTheory.Abelian.Ext.commShift_of_localization` theorem verbatim.
`Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` imports this module
and refers to that qualified declaration, so the helper is part of the required
import interface. The public theorem and its proof are unchanged.

## Proved and sorry left

`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison` remains completely
proved. No `sorry` is present, and no holes were added or split off. This repair
restores an interface declaration and makes no proof-progress claim.

## No longer needed

None. Both imports remain required, and the restored helper is required by its
direct importer. No DAG node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery removed `commShift_of_localization` after incorrectly
classifying it as unused. Its direct importer uses the fully qualified name, so
removing it causes an `Unknown constant` error. The helper is restored exactly as
in the known-good module; no target statement or public signature changed.

## New nodes

None.

## Second reading by Y3

1. Compared the delivered module with the repository version. The theorem statement and
   all existing declaration signatures are unchanged; only the helper restoration and an
   explanatory proof comment differ.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. There
   are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
   The recorded axiom check for `exactFunctorIdentityComparison` has no impermissible
   axioms.
3. No statements were split off and no new nodes were added, so there are no additional
   statements to validate.
4. The proof uses the existing identity specialization and composition comparison route;
   both imports remain necessary, and no shorter unused dependency was found. Restoring
   `commShift_of_localization` is required by its direct importer.
5. The node's Lean declaration, proof route, and dependency list agree with the module;
   the unit route is unchanged.

Changed after reading: restored the private `commShift_of_localization` helper and recorded
the corrected proof origin in the node; no theorem statement or public interface changed.
