## What changed

Proved `AlgebraicGeometry.fpqcCover_specMap_algebraMap_of_field` in
`Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover` without changing its signature or imports.
The first three conjuncts use Mathlib instances; the fourth uses
`AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage`.
Updated the existing node's proof to record these implementations of its four steps.
The unit's route is preserved.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.fpqcCover_specMap_algebraMap_of_field`
(node `lem-pc-field-extension-fpqc-cover`). No holes added; no sorry remains in the item.
The single-file compile passed without warnings. The delivery dry run checks axioms.
The argument applies to identity extensions and arbitrary extensions, including infinite
extensions: quasi-compactness follows from affineness, not finite generation.

## No longer needed

None. No imports removed and no proof-dependency nodes pruned. The three field-extension
supports are already Mathlib leaves, used through their instances; the fpqc definition and
all three properties remain needed. No new Sheaf dependencies were imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The generic singleton criterion is already in Mathlib and
makes the final affine-open argument unnecessary to repeat in Lean.
Searches actually run with msearch.py: LeanFinder for a flat surjective quasi-compact
singleton fpqc cover returned generic quasi-compact-cover tools; Loogle for
`AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage` returned its exact signature;
grep for `singleton_mem_fpqcPrecoverage` located Mathlib's Fpqc.lean:108.
Library rg found no duplicate of the field-extension theorem.
The unit record was read; its realized statement and steps are empty, and the proof retains
the field-extension fpqc fact used by the unit's ampleness-descent step. The literature
unit file at the record's source path is absent on this machine; its text is included in
the unit JSON and was read there.

## Second reading by T3

1. **Unchanged public contract — pass.** Diffed the sole delivered Lean module against
   the repository version. Only `:= sorry` became its proof; the existing signature,
   docstring, module header, namespace, universes and public import are byte-for-byte
   unchanged. There are no definition changes, added declarations or change records.
2. **Proof and axioms — pass.** Independently compiled the module with `lcompile.py`
   without errors or warnings (1.6 seconds). Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.fpqcCover_specMap_algebraMap_of_field`: exactly
   `propext`, `Classical.choice`, `Quot.sound`. No sorry or forbidden declaration remains.
   Read the Mathlib singleton criterion and the flatness, surjectivity and affine
   quasi-compactness instances used to discharge its hypotheses.
3. **Split statements — pass, none.** No new statements, nodes or holes were added.
   Checked identity extensions and unrestricted field extensions: both spectra have
   one point, the source is nonempty, flatness holds over the field target, and
   affineness implies quasi-compactness without a finite-generation assumption.
4. **Shortest route and pruning — pass.** The direct Mathlib instances and singleton
   criterion close all four clauses without importing any open Sheaf result. The sole
   public import defines `Scheme.fpqcPrecoverage`, which occurs in the signature, so
   it is required publicly. Independently searched Lean for alternate fpqc field-extension
   declarations and Mathlib through msearch grep for `algebraMap.*singleton`,
   `singleton.*algebraMap` and `of_isField`; no shorter packaging was needed. All four
   old proof dependencies remain used, including the three Mathlib leaves, so the
   report's pruning list is complete. Read `dag/units/sk-thm-picard-rr.json`: its
   `realized` lists are empty; its ampleness-descent step still uses precisely the
   field-extension fpqc fact supplied here. No unit route is bypassed.
5. **DAG agreement — pass.** Diffed the existing node and read every proof dependency.
   Only `proof` and `proof_origin` changed. The four steps describe the actual Mathlib
   implementation, and `proof_deps` is their union. The dependencies' recorded Mathlib
   specializations agree with the instance proofs. No new-node fields are required.

Second reading changed only this report: added independent verification and the
second-reading verdicts. The Lean proof and node repair are accepted unchanged.
