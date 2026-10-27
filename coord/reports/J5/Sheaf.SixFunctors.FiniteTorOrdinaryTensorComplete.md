## What changed

Replaced the assigned theorem's single `sorry` by the affine-chart argument of
Bhatt--Scholze Lemma 6.5.5. The statement, coefficient ring, ordinary tensor and
completion predicate are unchanged. The proof obtains common input models,
represents their tensor by a bounded finite-projective total complex, proves that
complex complete, transports along its actual isomorphism, and descends.

Added four statement modules and their nodes. The bounded-projective completeness
module contains a proof from the existing completed-free-cell theorem and the
intrinsic local-Hom criterion: the kernel of exact restriction followed by internal
Hom is triangulated; finite free cells vanish, retracts vanish, and bounded
homotopy-category devissage applies. The tensor-model module constructs the
recorded pro-etale tensor presentation, identifies the canonical completed-ring
pullbacks by their quotient projections and adjoint/derived uniqueness, and uses
the existing canonical tensor-pullback comparison. Its finite totalization and
termwise finite-free splittings are proved explicitly. The two geometric steps
are stated separately below. No existing module except the assigned one changes.
The original public imports are preserved; new proof imports are private.

## Proved and sorry left

Original holes: 1. Closed the body of
`WeilConjectures.GeneratorReduction.finiteTorOrdinaryTensorComplete`.
Added holes: 2, so this is a decomposition, not a net sorry reduction.

The new theorems
`WeilConjectures.GeneratorReduction.boundedProjectiveComplex_complete` and
`WeilConjectures.GeneratorReduction.projectiveChartOrdinaryTensorModel` have no
`sorry` in their proofs. Every remaining hole introduced by this packet is:

- `WeilConjectures.GeneratorReduction.finiteTorAffineProjectiveCharts`, node
  `lem-sf-finite-tor-affine-projective-charts`: common input models only, without
  any tensor conclusion.
- `WeilConjectures.GeneratorReduction.affineTreeCompleteDetection`, node
  `lem-sf-affine-tree-complete-detection`: a locality criterion for an arbitrary
  ambient object, without constructibility, boundedness or tensor hypotheses.

These are different genuine steps of the argument, and neither is the assigned
statement repackaged. No data definition contains a hole or chooses an arbitrary
object from an unproved mere existence theorem. The final proof only eliminates
existentials while proving a proposition. Rank zero, zero complexes, inverted
support bounds, empty schemes and empty leaves are included.

Validation: the clean server `lcompile.py --all` run compiled all five modules.
Times were 26.9 s for locality, 4.2 s for bounded-projective completeness, 27.2 s
for common charts, 47.6 s for the tensor model and 36.5 s for the assigned module.
No profiler or trace option remains. Local irreducibility controls prevent
unnecessary unfolding of adjoints, derived functors and the chosen calculus; the
private pullback comparison is irreducible. No shared reducibility attribute changes.
The delivery command runs the required independent packet checks.

## No longer needed

No original public import is removed. The three old proof-dependency edges are
replaced; they were planned dependencies, not actual imports of the item:

- `lem-fix-bounded-projective-tensor-complete`, module
  `Sheaf.Paper.BoundedProjectiveTensorComplete`: has qcqs and residue-characteristic
  invertibility hypotheses absent from the item. Its generic finite-retract tensor
  calculations are reused as private proved helpers; the new bounded completeness
  proof uses free cells and local-Hom kernels without those hypotheses.
- `lem-fix-constructible-projective-chart-refinement`, module
  `Sheaf.Paper.ConstructibleProjectiveChartRefinement`: requires a qcqs base and
  `IsUnit (l : Γ(W, ⊤))`. The new input-chart step is on each affine open, with
  exactly the generality needed here and an inductive finite-tree interface.
- `lem-fix-qcqs-completion-unit-locality`, module
  `Sheaf.Paper.QcqsCompletionUnitLocality`: also requires that global unit
  hypothesis. The new geometric detection step includes affine descent and has
  no residue-characteristic restriction.

This prunes these three edges from this item's route. Other users of those
modules remain; none of their declarations or files is withdrawn. No blueprint
unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned theorem is about arbitrary schemes and imposes no invertibility of
ell on them. All three old planned dependencies require invertibility, and the
item has no hypothesis from which it follows (even the zero inputs exist in
residue characteristic ell). They therefore do not directly prove the stated
item. Lemma 6.5.5 in the supplied Bhatt--Scholze source works with an arbitrary
complete noetherian coefficient ring; its Section 6.5 makes no such invertibility
assumption. The replacement keeps the item unchanged and separates the input
model and geometric locality steps needed at that generality. The generic
canonical completion-unit criterion already has the required generality and is
used unchanged.

## New nodes

`lem-sf-finite-tor-affine-projective-charts` states only simultaneous bounded
finite-projective representatives for the two inputs on affine finite-tree
covers. Its complete source proof is in its docstring and node.

`lem-sf-affine-tree-complete-detection` states generic completeness detection by
those geometric covers. It has no finite-Tor, constructible or tensor assumption;
its docstring spells out unit compatibility, cover conservativity, empty leaves,
open-closed induction and affine descent.

`lem-sf-bounded-projective-complex-complete-unrestricted` records the proved
bounded-projective completeness calculation, with independent site and coefficient
universes and no geometric hypotheses.

`lem-sf-projective-chart-ordinary-tensor-model` records the proved algebraic
finite-total-tensor model comparison. It asserts no completeness result and uses
no completeness theorem.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
