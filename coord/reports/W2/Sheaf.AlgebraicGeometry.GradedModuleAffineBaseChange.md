## What changed

Replaced the original two-auxiliary composition with a genuine reduction of
`AlgebraicGeometry.exists_finiteType_graded_module_affine_baseChange` to the construction
of a finite quasi-coherent module over `pi_* O_Y` on X. The new module is
`Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChangeAlgebra`, with theorem
`AlgebraicGeometry.exists_finiteType_graded_algebra_module`. The target uses the existing
`Scheme.Modules.affine_module_correspondence` and `Scheme.Modules.affine_module_finite_type`
to construct the module on Y and transport finite type through an algebra-linear isomorphism.
All existing declaration signatures and definitions are unchanged. No change record is needed:
there is no existing interface change, public import change, or forced adaptation.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.exists_finiteType_graded_module_affine_baseChange`
(node `lem-weil-pbc-graded-module-affine-base-change`).

Hole added: `AlgebraicGeometry.exists_finiteType_graded_algebra_module`
(node `lem-weil-pbc-graded-module-affine-base-change-algebra`). Its complete proof in words
is in its docstring and its node. It constructs the algebra module on X; it does not
construct the module on Y or carry out the inverse affine correspondence.

This is a decomposition: one upper hole closed and one strictly intermediate hole added,
so the delivery itself has zero net holes closed. The target also depends on the open
upstream finite-type criterion. It is not axiom-complete. The two first-worker auxiliary
holes `exists_qcoherent_graded_module_affine_baseChange` and
`finiteType_of_graded_generators` were removed from this unlanded delivery; neither is
claimed as a hole closed against the library baseline.

## No longer needed

The target's direct proof-dependency imports of
`Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`,
`Sheaf.AlgebraicGeometry.AssociatedModule`, `Sheaf.AlgebraicGeometry.TensorPullback`,
`Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` moved to the algebra-module
construction, where the original construction plan still uses them. They remain in the
import closure. No library module is asserted globally pruned.

Every original dependency absent from the target's new direct `proof_deps` is accounted for:
`def-weil-pbc-associated-module`, `def-pc-module-pullback`,
`lem-weil-pbc-affine-morphism-relative-spec`, `lem-weil-pbc-relative-spec-base-change`,
`lem-weil-pbc-quasi-coherent-module-coproduct-closure`,
`def-weil-presheaf-modules-sheafification`, and
`def-weil-pbc-module-finite-type-presentation` now occur in the new intermediate node's
`proof_deps`. The affine-morphism and affine-correspondence dependencies remain direct.
The first-worker modules `GradedModuleAffineBaseChangeAux` and
`GradedModuleAffineBaseChangeAux2` and their two unlanded nodes were removed.

## Where the brief, the DAG or earlier work was wrong

The first worker's `finiteType_of_graded_generators` is false. The isomorphism `e` only
identifies O_X-modules, and supplies no compatibility between F's algebra action and `mu`.
A concrete counterexample is A = k, B = k[t] with its usual grading, X = Spec(k), and
G_m = O_X for every m. Let `mu` act by the coefficient of a homogeneous polynomial.
The element 1 in G_0 generates this graded module under `mu`, so all the homogeneous
finite-generation hypotheses hold. Let F on Spec(k[t]) be the associated module of the
countable direct sum of k, with t acting by zero. Its pushforward to Spec(k) is the
countable coproduct of O_X, hence has the asserted ordinary pushforward isomorphism.
But F is not finite type: a finite set spans a finite-dimensional k-subspace because
its k[t]-action factors through k, whereas its underlying k-space is infinite-dimensional.
This counterexample even has canonical b and quasi-coherent F.

The first-worker docstrings did not give complete proofs. Both new nodes copied the whole
target natural-language statement instead of stating their own Lean propositions, and the
target node did not record the changed proof dependencies. These faults are repaired.
The source is the realization paragraph of [Stacks Tag 0897](https://stacks.math.columbia.edu/tag/0897),
with [Tag 01SB](https://stacks.math.columbia.edu/tag/01SB) and
[Tag 01PB](https://stacks.math.columbia.edu/tag/01PB). The omitted homogeneous-action
construction and local-generation details are supplied in the new docstring.

## New nodes

`lem-weil-pbc-graded-module-affine-base-change-algebra` realizes precisely original
construction steps 1-3: extend the homogeneous action to the direct image algebra, prove
quasi-coherence, and prove local finite generation over that same action. It has the
original node's chapter and unit, a self-contained statement, a verbatim Lean signature,
a full natural-language proof, source, proof-dependency union, origin and creation record.
Fresh Loogle, Lean Finder and Mathlib grep searches found no matching construction;
LeanSearch was unavailable and is recorded without an absence verdict. Searches in both
Lean roots found only graded algebra infrastructure, the cohomological graded results,
and the affine correspondence already used for the final step.

## Second reading by W2

1. Compared every delivered module with the read-only repository version. The existing
   target signature is byte-for-byte unchanged; no definition, hypothesis, conclusion,
   visibility or public import was changed. The algebra module is new. No other existing
   module is adapted. Verdict: pass after replacing the faulty decomposition.
2. Compiled both final modules through lcompile.py in import order without errors or
   warnings. The sole remaining sorry is the complete body of the public new theorem;
   there are no forbidden declarations and no holed definitions. An appended scratch
   `#print axioms` check confirms only the standard axioms and sorryAx from open statements.
   Verdict: valid reduction, not a completed proof.
3. Rejected the old finite-type theorem by the counterexample above. Checked the replacement
   on zero modules, the empty scheme, grading concentrated in degree zero, and the polynomial
   example. In each case its conclusion is the finite algebra module supplied by the given
   action, not an unrelated module on Y. The statement is a proper construction stage and
   the target performs the remaining correspondence step using existing library theorems.
   Its source and full proof in words are present; fresh searches found no duplicate.
   Verdict: pass; one honest construction hole remains.
4. Checked the route from the target downward. The final step now invokes the existing
   affine correspondence and finite-type criterion. Original construction dependencies
   moved to the split node rather than being silently discarded. The unit
   `dag/units/sk-thm-p1.json` realized statement and all four realized steps are preserved;
   no unit or chapter argument was bypassed. Verdict: pass; no global pruning claimed.
5. Updated the original node's proof and exact proof-dependency union. The new node matches
   its Lean declaration and records original construction steps 1-3, with its searches,
   source, chapter, unit, origin and creation fields. Removed the mismatched old new nodes.
   Verdict: pass.

Second reading changed: removed the false finite-type auxiliary and the incomplete
quasi-coherent auxiliary; replaced them with one algebra-module construction theorem;
proved the target's final step using the existing correspondence and finite-type criterion;
updated DAG records, imports, docstring and progress accounting.
