## What changed

Proved `Algebra.TensorProduct.finite_purelyInseparable_of_tensorProduct` without changing its signature.
Added proof-only imports of Mathlib dual lemmas and flatness; these also provide
the dimension constructions and finite-dimensional results transitively. Updated the theorem's proof explanation and its DAG proof route.
The proof uses finrank preservation, injectivity of the tensor inclusion, the finite-dimensional
domain field construction, and a linear functional on L sending 1 to 1. Applying its tensor
extension to each purely inseparable power equation proves descent in all characteristics.

## Proved and sorry left

Closed the one original hole:
`Algebra.TensorProduct.finite_purelyInseparable_of_tensorProduct`
(node `lem-weil-pbc-finite-purely-inseparable-scalar-descent`).
No holes added, no holes left, and no decomposition. All ingredients are proved in Mathlib.

## No longer needed

No original import removed: all three public imports serve the unchanged statement.
The explicit dependency `lem-weil-pbc-vector-space-basis-through-vector` is pruned:
a basis of B containing 1 and its coordinate comparison are not used. That node has no
Sheaf module (it is a Mathlib leaf). The characteristic-zero dimension-one branch is also
unnecessary: the exponential-characteristic criterion handles it with q = 1.
All other previous proof dependencies still provide the notions or Mathlib results used.
Second reading removed the redundant proof imports
`Mathlib.LinearAlgebra.Dimension.Constructions` and
`Mathlib.LinearAlgebra.FiniteDimensional.Basic`; their declarations remain available
through `Mathlib.LinearAlgebra.Dual.Lemmas`.
No unit statement or realized step is bypassed; this item is below the unit level.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The earlier basis route was correct but longer than necessary.
A linear functional on L with f(1)=1 suffices, and finrank positivity yields finiteness
without manually constructing or counting a scalar-extended basis. The functional is
obtained from a fully proved Mathlib theorem, so no arbitrary data is taken from a hole.

## Second reading by V1

1. Compared every delivered Lean module against the repository. The sole theorem's signature
   is byte-for-byte unchanged; no definition changed and no change record is needed. Pass.
2. Compiled the module cleanly using `lcompile.py`. A scratch copy with `#print axioms`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`. No holes, forbidden
   declarations, or hollow definitions occur. The functional and field structure come
   from proved Mathlib constructions. Pass.
3. No statements were split off and no new nodes were added. Searched the library and
   Mathlib with tensor/purely-inseparable and descent/base-change terms; no shorter
   theorem matching this descent conclusion was found. Checked characteristic zero
   (q = 1), the identity scalar extension, and the excluded zero-algebra case. Pass.
4. The linear retraction gives a shorter route than basis coordinate comparison.
   Removed two redundant proof imports and confirmed the remaining added imports are
   necessary by compiling scratch copies without each. The original public imports
   remain unchanged. The old proof-dependency list loses exactly the basis-through-vector
   node named above. Checked `dag/units/sk-thm-p1.json`: no realized step is bypassed. Pass.
5. Read the node with the proof: its four steps, dependency union, and agent proof origin
   match the Lean argument and Mathlib leaves. Only the permitted proof metadata changed;
   no statement, statement dependency, or unit route changed. Pass.

Second reading changed the Lean imports by removing the redundant dimension-constructions
and finite-dimensional-basic imports, and corrected the report to describe this pruning.
The proof itself required no repair; no additional hole was closed or introduced.
