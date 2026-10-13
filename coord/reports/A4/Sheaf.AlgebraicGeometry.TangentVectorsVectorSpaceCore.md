## What changed
Proved `AlgebraicGeometry.tangentVectors_core` directly from the existing proved
`AlgebraicGeometry.existsUnique_dualNumberScheme_extension`, specialized to two
copies. Constructed the pushout universal property, applied unique gluing to
compatible tangent vectors, and proved base compatibility by pushout hom-ext.
The theorem signature and all public imports remain unchanged. Added proof-only
imports of Mathlib's IsPullback.Basic and FinCases; retained the existing
DualNumberSchemePushout proof import. Updated the existing node's proof steps
and origin; its proof dependency remains `lem-sc-dual-number-scheme-pushout`.

## Proved and sorry left
Closed the original hole in `AlgebraicGeometry.tangentVectors_core`
(node `lem-sc-tangent-vectors-core`): 1 of 1 original holes closed.
No holes remain in the item and none are added. Removed all three proposed
split theorems from the previous sandbox attempt; this is a proof, not a
three-hole decomposition. Single-file compilation passes without warnings.

## No longer needed
The previous sandbox's three proof imports and proposed modules
`Sheaf.AlgebraicGeometry.TangentVectorsCorePushout`,
`Sheaf.AlgebraicGeometry.TangentVectorsCoreGluing`, and
`Sheaf.AlgebraicGeometry.TangentVectorsCoreOverBase` are unnecessary.
Their proposed nodes `lem-sc-tangent-vectors-core-pushout`,
`lem-sc-tangent-vectors-core-gluing`, and
`lem-sc-tangent-vectors-core-over-base` are omitted from this delivery.
No import from the repository version is removed and no existing unit is bypassed.

## Where the brief, the DAG or earlier work was wrong
The previous decomposition left three holes although the existing finite-copy
extension theorem proves all three components with elementary category-theory
and ring-map glue. That decomposition is replaced by the complete direct proof.
The unit record has no realized statement or proof-step nodes that this route
would bypass. The previous second-reading report has been removed because it
reviewed the superseded decomposition; the next reader must review this proof.

## Second reading by A4
1. Compared the delivered module and node with the repository. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof text, proof-only imports, and proof metadata changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it has no errors, warnings, `sorry`, or forbidden declarations. `#print axioms AlgebraicGeometry.tangentVectors_core` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the direct proof against the existing `existsUnique_dualNumberScheme_extension` declaration and searched the library and Mathlib for duplicates. No split-off statements or new nodes are introduced, and the target theorem is unchanged. Verdict: pass.
4. The proof specializes the imported finite-copy extension theorem, then uses `IsPushout.mk'` and `IsPushout.hom_ext`; this is the shortest available route and removes the earlier unnecessary decomposition. The retained `DualNumberSchemePushout` import is needed for the extension theorem; the two new imports are proof-only. Verdict: pass.
5. The node proof steps and `proof_deps` match the Lean proof, with the original unit route retained and no realized unit step bypassed. Verdict: pass.

Changed during second reading: no mathematical changes; verified compilation and axioms, and added this review record.
