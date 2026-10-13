## What changed

Wrote a complete proof of `AlgebraicGeometry.Etale.etaleRestrictedSections_comparison_map`
in `Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparisonMap`, preserving its signature
and its original public import. Added a proved private helper `restricted_iso_formula`,
which calculates the explicit finite-diagonal comparison on a nonnegative-resolution summand.
The helper follows the calculation already proved in
`Sheaf.CategoryTheory.CartanEilenbergMappedTotal`, without importing that module or using
its existence theorem. The main proof cancels the restricted comparison isomorphism,
checks equality on total summands, uses `T.w_formula`, and cancels the extension isomorphisms.
Negative resolution summands are zero. No restriction on the integer truncation threshold
or on the number of nonzero diagonal terms is added.

## Proved and sorry left

One original hole replaced by a complete proof:
`AlgebraicGeometry.Etale.etaleRestrictedSections_comparison_map`
(node `lem-weil-pbc-etale-restricted-sections-comparison-map`). No new holes or nodes.
There is no `sorry` in the delivered source or its private helper.

Validation: the complete proof first compiled in an isolated scratch experiment. During
the delivery dry run, the shared cache became available and the actual assigned module
compiled. An empty line inside the proof triggered a style warning; it has been removed.
The final delivery dry run verifies the actual module and probes its axioms.

## No longer needed

No imports removed. No node or module pruned. The proof follows the existing node plan.
The augmentation commutation theorem `etaleRestrictedAugmentation_inclusion` is not used;
its module remains necessary because it defines `etaleRestrictedTotalInclusion`, which occurs
in the unchanged statement. No K-injectivity or cohomology-isomorphism theorem is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The compiled cache initially lacked the direct
import `Sheaf.AlgebraicGeometry.EtaleRestrictedAugmentationInclusion`, causing the compiler
to stop before checking any proof. The import became available during the delivery dry run.
No build or cache tool was modified. No duplicate library module is part of this delivery.

## Second reading by W2

1. Compared the delivered module with the repository version. The theorem signature and public import are unchanged; only the proof and a private helper were added.
2. Compiled the module with `lcompile.py`; it compiled successfully with no errors or sorries. The proof uses no forbidden declarations, and its helper is private and fully proved.
3. The existing theorem is unchanged and no new statements or nodes were introduced, so there are no split-off claims to validate.
4. The proof follows the finite-diagonal total comparison route in the node and keeps the unit route; no imports or nodes were pruned.
5. The DAG node's theorem name and statement match the Lean declaration, and the report's proof description matches the implemented calculation.

Changed only the proof, adding the private `restricted_iso_formula` calculation helper; no statement, definition, import, or DAG node was changed.
