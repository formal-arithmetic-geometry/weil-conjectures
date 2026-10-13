## What changed

Proved `Algebra.fibre_dimension_le_of_quasiFinite_polynomial_localization` in the assigned
module without changing its signature or public imports. Added the fully proved private
helper `Algebra.polynomial_factorization_baseChange`, which constructs the scalar-extended
polynomial map and proves finite type and quasi-finiteness from the existing four-rings
theorem. Its algebra map is constructed explicitly, not chosen from an unproved existence
statement.

Added proof imports `Mathlib.RingTheory.TensorProduct.MvPolynomial`,
`Mathlib.LinearAlgebra.TensorProduct.Finiteness`, and
`Mathlib.RingTheory.Localization.BaseChange`. Both original Sheaf proof imports remain used.
Updated only the assigned node's `proof`, `proof_deps`, and `proof_origin` to match the Lean.
No definitions, statements, other modules, or unit records were changed.

The proof follows [Stacks 00QH](https://stacks.math.columbia.edu/tag/00QH), using
[00PN](https://stacks.math.columbia.edu/tag/00PN) for scalar extension and
[00QG](https://stacks.math.columbia.edu/tag/00QG) for the dimension bound. These pages were
read online because the literature checkout is absent. The principal open of the image of
`g` is used directly in the infimum defining local dimension. The finite-type hypothesis
on the fibre algebra is obtained by composing the polynomial algebra with the finite-type
map supplied by the four-rings theorem.

## Proved and sorry left

Closed the sole original hole:
`Algebra.fibre_dimension_le_of_quasiFinite_polynomial_localization`
(node `lem-weil-pbc-fibre-dimension-bound-of-polynomial-factorization`).
Also fully proved the private helper `Algebra.polynomial_factorization_baseChange`.
No `sorry` remains in the delivered module; no holes or modules were added.

This is a proof from existing declarations, not a new decomposition. The existing
`AlgebraicGeometry.topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial`
(node `lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra`) still has `sorry` in its
source module outside this delivery and remains a needed dependency. The four-rings
source theorem is already proved.

Single-file compilation passed without warnings. The helper works for an arbitrary
commutative scalar algebra, including the zero ring. The final argument does not require
an injective polynomial map. For `n = 0` all finite-type and dimension steps are unchanged;
when `D(g)` is empty there is no point satisfying `hg`. No extra hypothesis was introduced.

## No longer needed

Removed from this node's proof dependencies:

- `lem-weil-pbc-tensor-cancel-base-change`: the explicitly constructed polynomial map and
  finite-sum tensor representation allow direct use of the existing four-rings theorem.
  No separate tensor-cancellation isomorphism is needed.
- `lem-weil-pbc-dimension-at-point-open-subspace`: the principal open itself is used as
  an open neighbourhood in the infimum, without transferring local dimension by equality.

Neither of these dependencies had a separate proof import in the original module, so no
original import was removed. `WeilConjectures.Mathlib.Topology.KrullDimension` remains
required for `topologicalKrullDimAt`. All other original node dependencies remain used.
Temporary imports of `Mathlib.RingTheory.FiniteStability` and
`Mathlib.RingTheory.Localization.Away.AdjoinRoot` were eliminated: finite type of the
localized fibre follows directly through its polynomial factorization. No Sheaf module
is asserted globally unreachable; other items may still use the pruned nodes.
The unit's own realized statement and steps remain intact.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's tensor-cancellation and local-dimension-equality
steps were valid but unnecessary for the bound. The existing theorem docstring describes
that longer valid route; the updated node describes the implemented shorter route.
The brief's requested `coord/delivery-errors.md` section I is absent in this checkout;
the existing delivery-error sections were read instead.

## Second reading by J3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof code and plain proof imports were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the helper is a concrete tensor-product construction. Verdict: pass.
3. Checked the private helper and the target argument against the fibre, localization, and quasi-finiteness hypotheses, including zero rings, `n = 0`, and empty principal opens. No statement was split off and no hypothesis or conclusion was changed. Verdict: pass.
4. The proof uses the direct scalar-extension construction and principal-open infimum argument, which is shorter than the prior tensor-cancellation and open-subspace-equality route. The removed proof dependencies are recorded above, and the unit route and realized records remain unchanged. Verdict: pass.
5. The node proof, proof dependencies, and proof origin match the implemented route; no new nodes or changes are needed. Verdict: pass.

I changed only this second-reading report section; no Lean declarations or DAG statements were changed during review.
