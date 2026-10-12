## What changed

Proved `ExteriorAlgebra.exists_koszul_conormal_comparison_map` with its statement,
visibility and docstring unchanged. The proof follows all three steps of
`new-s3-koszul-conormal-comparison-map`: obtain the existing conormal basis,
construct the signed top evaluation map explicitly, kill the incoming differential,
and verify the determinant normalization.

Three proved private helpers compute conormal coordinates, evaluate a top functional
using `AlternatingMap.eq_smul_basis_det`, and show that evaluating the top Koszul
boundary belongs to the ideal. The latter uses the existing `koszul_differential`
formula and identifies its differential with contraction by its uniqueness clause.
`ModuleCat.semilinearMapAddEquiv` implements restriction of scalars, and
`HomologicalComplex.mkHomToSingle` constructs the cochain map.

Added the proof-only import `Mathlib.LinearAlgebra.Determinant`. Removed two redundant
proof imports, listed below. No definitions, public signatures, node statements or
unit steps changed; the DAG's existing construction and three proof steps are retained.

## Proved and sorry left

Closed the sole original hole:
`ExteriorAlgebra.exists_koszul_conormal_comparison_map`
(node `new-s3-koszul-conormal-comparison-map`).

The delivered module contains no `sorry`. No holes were added or split off, and all
three private helpers are proved. The proof uses the existing theorem
`ExteriorAlgebra.exists_koszul_conormal_basis`; its existing transitive proof obligations
are unchanged and are not part of this delivery.

The explicit construction handles rank zero, the unit ideal and the zero ring without
extra hypotheses. In rank zero there is no incoming differential; determinants are
empty determinants. For the unit ideal the quotient and determinant module are zero.
The basis theorem fixes every basis vector, so the basis data is determined, rather
than an arbitrary witness of an unproved mere-existence statement.

## No longer needed

Removed direct imports `Sheaf.Paper.KoszulComplex` and
`Sheaf.RingTheory.KoszulDualComplex`: their public declarations remain available through
the unchanged statement imports. Their mathematical definitions are still used.
No mathematical dependency nodes or modules are pruned from the target closure.
The conormal-basis dependency and the exterior-power determinant pairing are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The prescribed three-step argument can be completed
without new intermediate obligations. The cited local source file
`literature/stacks-project/duality.tex` is absent from this checkout; this delivery
implements the existing declaration's detailed proof and the DAG plan, with the
contraction formula and determinant pairing checked against their Lean declarations.

Validation: the final module compiles cleanly with `lcompile.py`, without warnings.
The delivery dry run is the final mechanical check; no delivery is pushed by this worker.

## Second reading by J2

1. Compared the delivered module with the repository version. The existing theorem signature and all public declarations are byte-for-byte unchanged; only the proof and proof-only imports differ. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked for forbidden constructs and `sorry`; it compiles cleanly and contains no local holes, axioms, unsafe declarations, or hollow definitions. The target's transitive `sorryAx` dependencies are unchanged. Verdict: pass.
3. Reviewed the construction and helper lemmas, including rank-zero, unit-ideal, and zero-ring cases. The helpers are private reductions, true, and strictly simpler than the target; no duplicate Mathlib or library theorem and no new split-off statement was added. Verdict: pass.
4. Checked the proof from the target downward. It uses the existing conormal-basis and exterior-power pairing declarations, follows all three DAG steps, and removes only the two redundant proof imports. Verdict: pass.
5. Checked the node proof, dependencies, origin, and unit route against the Lean proof. The node remains the same target node, its declared dependencies are used, and the unit `sk-thm-picard-duality` route is preserved. Verdict: pass.

Changed in this second reading: no mathematical or interface changes; this section records the review required by stage 3.
