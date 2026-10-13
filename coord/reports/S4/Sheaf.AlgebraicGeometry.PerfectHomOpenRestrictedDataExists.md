## What changed
Added two intermediate theorem modules. The target now combines the restricted QCoh
fields with the restricted representing-data construction.

## Proved and sorry left
`perfect_hom_open_restricted_data_exists` is reduced to the two named intermediate
statements. Sorries remain in `perfect_hom_open_restricted_core_exists` (node
`new-perfect-hom-open-restricted-core`) and `perfect_hom_open_restricted_qcoh`
(node `new-perfect-hom-open-restricted-qcoh`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original one-step construction was split into the construction and its QCoh
obligations so the target proof is a real assembly.

## New nodes
`new-perfect-hom-open-restricted-core` and `new-perfect-hom-open-restricted-qcoh`.

## Earlier second reading (a previous round; superseded)
The target proof is a direct assembly from the two strictly smaller named statements;
the restricted core carries the representing maps and equivalences, while the QCoh lemma
supplies only the two omitted fields.

## Second reading by S4

1. Compared the delivered target module with the repository version. The target statement is byte-for-byte unchanged; only proof imports and the proof body differ.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The two intermediate theorems remain the only named `sorry`s, and there are no sorries in definitions or forbidden declarations.
3. Checked the split statements and their docstrings. The QCoh statement is a strict, true component proved from the existing open-restriction QCoh theorem. The core statement is the remaining construction conditional on exactly those QCoh fields, with its construction proof recorded in the docstring. No duplicate library theorem was found.
4. The proof follows the shortest available route: open-restriction QCoh is proved directly from `schemeDerivedQCoh_openRestriction_iff`, then the target assembles the two strictly smaller statements. The QCoh module's unnecessary public import of the core module was removed.
5. Updated the DAG proof and proof dependencies to match the Lean proof, including the existing open-restriction QCoh node and both split nodes. The unit route remains represented by the target node and its construction component.

Changed: proved `perfect_hom_open_restricted_qcoh`; retained `perfect_hom_open_restricted_core_exists` as the named construction hole; updated imports, DAG proof metadata, and this review record.
