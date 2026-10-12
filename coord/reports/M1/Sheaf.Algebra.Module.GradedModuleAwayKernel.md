## What changed

Replaced the sole sorry in `Sheaf.Algebra.Module.GradedModuleAwayKernel` by a complete proof.
A proved private helper `LocalizedModule.awayKernelFraction` clears an arbitrary source
denominator and detects numerator torsion using Mathlib `LocalizedModule.mk_eq`.
Its fraction-power computation proves both the module and ring kernel claims.
The ring homomorphism is viewed as an S-linear map so the same calculation applies with M=S.
The existing theorem signature, visibility, definitions, docstring, and imports are unchanged.
Updated the node's proof, proof_deps, and proof_origin to record this shorter route.

## Proved and sorry left

Closed: `LocalizedModule.gradedModuleAwayKernel`
(node `lem-weil-pbc-graded-module-away-kernel`), including both conjuncts.
Also proved the private helper `LocalizedModule.awayKernelFraction`.
Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
Single-file compilation succeeds without warnings. The delivery dry run checks axioms.

## No longer needed

No import can be removed: both public imports remain necessary for the unchanged statement.
No modules are pruned from the target import closure.
Removed `def-sc-degree-zero-module-fractions` from proof_deps only: its definition remains
needed by the statement, but its equal-degree representation is unnecessary for this proof.
The planned homogeneous relation, explicit restriction fraction formula, inverse formula,
uniqueness, bijectivity, semilinearity, and unit hypotheses require no proof dependencies here.
Clearing the source denominator first replaces the planned computation using g^e=a*f.
The unit's statement and realized proof steps are not bypassed or modified.

## Second reading by M1

1. Compared the delivered module with the repository version. The theorem signature,
   visibility, definitions, docstring, and public imports are unchanged; only a private
   helper and the two proofs were added.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. There
   are no `sorry`, axioms, unsafe declarations, or hollow definitions. The proof uses the
   ordinary localization zero criterion and handles both conjuncts.
3. No statements were split off and no new nodes were added. The existing node statement
   is unchanged and its proof metadata records the declarations actually used.
4. Checked pruning and imports. Both public imports are required by the unchanged
   statement; the old degree-zero-fractions proof dependency is not used by the proof and
   is removed from `proof_deps`. The unit route and its realized fields remain intact.
5. Checked the mathematical route against the node and source. Clearing the source
   denominator, applying `LocalizedModule.mk_eq`, and factoring the positive degree give
   exactly the module and ring kernel conclusions, including nilpotent and zero-ring
   cases. Verdict: the proof establishes the original statement without weakening it.

No further changes were needed in this second reading.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt incorrectly treated missing proved graded denominator calculations as
an obstacle. The ordinary-localization zero criterion suffices: linearity and preservation
of b/1 detect numerator torsion directly. The DAG's original longer argument is valid but
unnecessary. This proof uses no unproved theorem and creates no new nodes.
The argument uses only positive d, and never cancels original-ring elements; zero rings,
nilpotent denominators, and exponent n=0 are all covered by the same Lean proof.
