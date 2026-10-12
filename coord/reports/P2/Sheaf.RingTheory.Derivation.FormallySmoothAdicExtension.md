## What changed

Completed `Derivation.exists_extension_of_formallySmoothAdic` in
`Sheaf.RingTheory.Derivation.FormallySmoothAdicExtension`, with its signature unchanged.
Added the proof-only import `Mathlib.Algebra.DualNumber`. The three private helpers
`dual_mem_smul`, `dual_complete`, and `dual_mem_map` are proved from Mathlib.
The proof constructs the twisted structure map explicitly, proves square-zero and
closedness of the projection kernel, invokes the existing complete-ring lifting
lemma, and constructs the derivation from the lift's second coordinate.
No public definition, existing signature, or visibility changed; no adaptations.

The source argument is [Stacks 07PL](https://stacks.math.columbia.edu/tag/07PL),
using [Stacks 07NJ](https://stacks.math.columbia.edu/tag/07NJ). The sandbox node copy
updates the concrete realization of steps 1, 3, 4, and 6 and its proof dependencies.
The unit `sk-thm-p1` has no realization in this item; its fixed steps are preserved.

## Proved and sorry left

Closed one hole: `Derivation.exists_extension_of_formallySmoothAdic`
(node `lem-weil-pbc-fs-adic-lift-derivation`). There are no sorries left in the
item and no new holes or new modules. All three private helpers are proved.
This is a proof from the existing declaration
`Algebra.FormallySmoothAdic.exists_lift_into_complete`, not a new decomposition.
Its existing downstream proof dependencies remain the next work; this delivery
does not claim the theorem is already independent of all downstream sorries.

The module compiled without errors or warnings using `lcompile.py`.
Completeness and closedness use no finiteness, nontriviality, locality, or
Noetherian hypotheses. The argument also covers `n = bottom` and the zero ring;
`n = top` under adic completeness forces the zero ring. No statement was weakened.

## No longer needed

Removed proof-dependency edge to `def-weil-polynomial-ring`, whose recorded
module is `Mathlib.Algebra.Polynomial.Basic`: concrete dual-number pairs replace
polynomial quotient construction and division. This removes that dependency
from this node, not a claim of global unreachability of the Mathlib module.
No original imports were removed: all four original imports are needed for
statements or the proof. All other original node dependencies remain necessary:
`def-weil-pbc-algebra-hom-quotient`, `def-weil-pbc-adically-complete-ring`,
`def-weil-pbc-formally-smooth-adic`, and `lem-weil-pbc-fs-adic-lift-into-complete`.
No other nodes or project modules become unnecessary on this route.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The polynomial-ring presentation in step 1 and
explicit inverse-limit product comparison in step 3 are unnecessary in Lean:
Mathlib provides the concrete pair ring, and coordinatewise Cauchy limits prove
completeness directly. The adic complete-ring lift remains essential; discrete
formal smoothness alone does not lift the identity when `n` is not nilpotent.

## Second reading by P2

1. Compared the complete module and node with the repository using `diff`.
   The sole existing declaration's signature is byte-for-byte identical, as
   independently checked by extracting its text. Its visibility and all public
   imports are unchanged. There are no definition changes or forced adaptations.
   Verdict: pass.
2. Independently compiled the delivered module with `lcompile.py`: no errors or
   warnings. Compiled a scratch copy with `#print axioms` for the main theorem
   and each private helper. The helpers use only `propext`, `Classical.choice`,
   and `Quot.sound`; the main theorem also uses `sorryAx` through the existing
   complete-ring lifting dependency. There is no local `sorry`, forbidden
   declaration, or hollow definition. The rings, ideals, quotient equivalence,
   and derivation are constructed explicitly; the existential lift is eliminated
   inside a proposition proof, not used to define arbitrary public data.
   Verdict: pass, with the reported existing dependency still open.
3. No statements were split off and no nodes were added. Reviewed the three
   proved private helpers: ideal membership follows from the two linear
   projections and the decomposition into scalar multiples of 1 and epsilon;
   completeness and separatedness follow coordinatewise. Checked the zero ring,
   bottom ideal, and top ideal (where completeness forces a subsingleton ring).
   No finite generation, locality, or Noetherian assumption is hidden.
   Verdict: pass.
4. Read the argument from the extension theorem downward. Independently searched
   Lean Finder for adic completeness of trivial square-zero extensions and
   lifting derivations under topological formal smoothness, and searched the
   library and Mathlib sources for alternate extension/completeness declarations.
   Mathlib's formally smooth complete-ring lift assumes discrete formal
   smoothness, which is not supplied here. Its square-zero derivation equivalence
   does not replace the required adic lifting theorem and would add machinery
   to the direct coordinate construction. The three public imports support the
   unchanged statement; both plain imports support the proof. The removed
   polynomial-ring edge is the only unused original proof dependency, and it
   is already listed under No longer needed. Read `sk-thm-p1.json`: this node is
   not a realization of its statement or any fixed step. Verdict: pass.
5. Compared the node fields: only `proof`, `proof_deps`, and `proof_origin`
   changed. Checked that `proof_deps` is exactly the union of the steps' `uses`.
   The concrete pair construction, coordinatewise completeness, closedness,
   quotient lift, and second-coordinate derivation match the Lean proof and the
   node's unchanged mathematical statement. There are no new-node obligations.
   Verdict: pass.

Second reading changed only this report, recording independent checks and the
axiom results. No repair to the Lean proof or node was necessary. Holes closed:
`Derivation.exists_extension_of_formallySmoothAdic` (one of one original holes).
Holes added: none. This closes the item's hole without asserting that its
transitive lifting dependencies are already free of `sorryAx`.
