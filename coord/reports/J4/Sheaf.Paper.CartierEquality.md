## What changed

Completed the proof of `cartier_equality` in `Sheaf.Paper.CartierEquality` using the existing finite transcendence basis, complete-intersection fraction-field cotangent model, and rank-nullity lemmas. No imports were changed.

## Proved and sorry left

The declaration `cartier_equality` is proved. No `sorry` remains in the item.

## No longer needed

None; all existing proof imports are used by the proof or by the statement.

## Where the brief, the DAG or earlier work was wrong

None.

## Second reading by J4

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the delivery only contains the completed proof and its proof-only imports.

2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. A scratch compilation reports that `cartier_equality` depends only on `propext`, `Classical.choice`, and `Quot.sound`, and there are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations.

3. The proof uses the existing finite transcendence-basis, complete-intersection fraction-field, cotangent-model, and rank-nullity results. No split-off statements or new DAG nodes were added, and the statement is already present in the library and is not duplicated or weakened.

4. Read the proof from the target downward: it constructs the finite basis and generators, applies the complete-intersection and cotangent equivalences, derives the dimension equation by rank-nullity and quotient dimension, and handles the finite-extension case by `trdeg_eq_zero`. The unit route through the complete-intersection and cotangent-model nodes is preserved.

5. Pruning check: `Mathlib.LinearAlgebra.Dimension.Constructions` was an unused proof import and was removed. All remaining imports are required by the statement or proof; no old proof dependency is otherwise removed.

Changed: removed the unused `Mathlib.LinearAlgebra.Dimension.Constructions` import, removed a dead local `have := hA`, and recorded this second reading.
