## What changed
Added the cotangent-condition intermediate theorem `Algebra.fieldExtension_cotangent_conditions` and used it to prove `Algebra.formallySmoothAtPrime_of_fieldExtension`.

## Proved and sorry left
The target theorem `Algebra.formallySmoothAtPrime_of_fieldExtension` is proved. The intermediate theorem `Algebra.fieldExtension_cotangent_conditions` remains `sorry`; it packages the faithful-flat descent of localized cotangent homology vanishing and differential projectivity (blueprint node `lem-weil-pbc-formally-smooth-at-prime-field-extension-descent-cotangent-conditions`).

## No longer needed
None; the module retained its original imports.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires substantial cotangent-complex descent not available as a single library theorem, so it was split into the named cotangent-condition intermediate result.

## New nodes
`lem-weil-pbc-formally-smooth-at-prime-field-extension-descent-cotangent-conditions` records the intermediate result.

## Earlier second reading (a previous round; superseded)
The reduction was compiled successfully; the intermediate statement is a strict conjunction of the two cotangent conditions needed to construct `Algebra.IsSmoothAt`.

## Second reading by Q2

1. Compared the delivered module with the repository version. The existing target signature is byte-for-byte unchanged; the only added declaration is the documented cotangent-condition split, and the unused local binding was removed.
2. Compiled the module with `lcompile.py`; it is clean. The target has no `sorry`; the only remaining `sorry` is the named `Algebra.fieldExtension_cotangent_conditions` theorem, with its matching node and source docstring. No forbidden declarations or hollow definitions were added.
3. Checked the split statement against the `FormallySmooth` constructor: it gives exactly projectivity of localized Kähler differentials and subsingleton first cotangent homology, with the same hypotheses and no weakening. The Stacks Tag 00TG source and the recorded searches support the statement; no existing library theorem duplicates it.
4. The target proof now uses only the split theorem, so the target node's proof and `proof_deps` were pruned to that node. The unit and its route remain unchanged; the split is below the unit level.
5. Checked the DAG/Lean agreement, including the new node's declaration and the target node's updated proof route. No imports were removed because both existing imports remain required by the module interface and statement.

Changed the target proof node metadata, removed an unused local, and recorded this second reading. No additional holes were introduced.
