## What changed

`Sheaf.Algebra.FiniteRelationCokernelColimit` now composes finite matrix lifting
and quotient comparison. Its existing signature is unchanged, and the new
imports are proof-only. Added `FiniteRelationMatrixLift` with a complete proof
and `FiniteRelationQuotientComparison` with one named open theorem. The target
DAG proof steps and dependencies now record this composition.

## Proved and sorry left

Closed the original hole `ModuleCat.exists_stage_finite_relation_cokernel` by
reducing it to a proved coefficient-lifting result and one open quotient result.
Proved `ModuleCat.exists_stage_finite_relation_matrix` without `sorryAx`.
Added one hole: `ModuleCat.finite_relation_quotient_comparison`, node
`lem-pc-finite-relation-quotient-comparison`. No other holes remain in the
three delivered modules. This is a decomposition, not an axiom-free proof of
the original theorem: one original hole closed and one new hole added, net zero.
The original theorem still depends on `sorryAx` through the comparison theorem.

## No longer needed

No imports removed from the original module. The original direct dependency
`lem-pc-filtered-colimit-commrings-elementwise` is now used transitively through
`lem-pc-finite-relation-matrix-lift`; its mathematics remains needed and no
module is pruned. Removed the unnecessary change-of-rings import and scoped
opening from the new matrix module; its public signature needs only ring
colimits and linear algebra. Its construction imports are proof-only.

## Where the brief, the DAG or earlier work was wrong

The first report referred to `exists_stage_colimit_element`, which is absent
from the original and delivered modules. It also counted both intermediate
claims as open, although the matrix lifting claim admits a short direct
Mathlib proof. The new nodes initially omitted namespace qualification and
verbatim Lean signatures, and their theorems lacked the required docstrings.
The quotient-comparison node incorrectly depended on matrix lifting: it takes
a matrix and coefficient equality as inputs and does not invoke lifting.

## New nodes

`lem-pc-finite-relation-matrix-lift`: finite coefficient lifting, now proved
using `Concrete.colimit_exists_rep`, `IsFiltered.sup_objs_exists`, naturality
of coprojections, and `Matrix.toLin'`. It is strictly the first subargument
of the original proof.

`lem-pc-finite-relation-quotient-comparison`: scalar extension of the quotient
of an already lifted matrix. Its docstring gives the complete right-exactness,
finite-free basis, and ULift transport argument. It is strictly the second
subargument and does not assert existence of a stage. No change records are
needed: no existing signature or definition changed.

## Second reading by R2

1. Compared every delivered existing module with the repository version by
`diff`. There is one existing declaration and its signature is byte-for-byte
unchanged. Only its proof and proof-only imports changed. The other two modules
are new. No definitions or target statements changed.
2. All three files compile without warnings using `lcompile.py --all`.
Scratch `#print axioms` checks show only `propext`, `Classical.choice`, and
`Quot.sound` for the matrix lemma, and additionally `sorryAx` for the comparison
and original theorem. Scanned for forbidden declarations and hollow definitions:
none. The only `sorry` is the named comparison theorem with source, blueprint
tag, proof in words, and matching node.
3. Read both intermediate statements against [Stacks Tag 05N7](https://stacks.math.columbia.edu/tag/05N7).
They are true and strictly smaller parts of the original argument. Checked zero
rows, zero columns, the zero ring, and a singleton indexing order: the matrix
proof handles empty coefficients with a receiving stage, and the comparison
uses right exactness, so it needs no injectivity or flatness. Searched with
fresh leanfinder, loogle, and grep queries (recorded in the nodes), and searched
Lean sources: no exact duplicate. Closed the matrix lifting hole directly.
4. The route is still finite matrix lifting followed by quotient comparison;
no unit-level route is bypassed. Read `dag/units/sk-thm-picard-semicon.json`:
its `realized` arrays are empty and were not altered. All remaining imports
serve signatures or proofs. The original elementwise node remains transitively
needed, so there are no pruned modules.
5. Corrected the original node to cite the two actual intermediate declarations.
Corrected new nodes to use qualified names and verbatim Lean signatures, and
removed the spurious matrix-lifting dependency from the comparison node.
The recorded sources and proof origins remain the original Stacks argument.

Second reading changed: proved matrix lifting; supplied the required theorem
docstrings; minimized the new matrix imports; repaired DAG declarations,
signatures and dependencies; corrected the report and decomposition count.
