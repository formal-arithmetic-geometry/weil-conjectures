## What changed

Replaced the proof hole in
`AlgebraicGeometry.source_fibre_differential_injective_of_formula` with a proof using
individual cotangent functionals. The public statement, including all let-instance
binders, is unchanged. The comparison-existence theorem is unchanged.

Validation: both modules compiled through the project compiler; the new module took
8.1 seconds and the main module took 8.6 seconds. The final unused simplification
argument reported by the compiler was removed before the delivery checks.

Two private helpers are completely proved: source-local differential germs span the
cotangent fibre, and scalar-extended coordinate functionals detect zero in a tensor
product. The first uses the existing relative-differential stalk equivalence and the
Kaehler differential generators. The second uses a basis and its scalar extension.
The main proof applies the displayed formula on the spanning germs and then applies
the coordinate calculation to the kernel.

Added the proof imports `Sheaf.AlgebraicGeometry.RelativeDifferentialsStalk`,
`Sheaf.AlgebraicGeometry.SourceFibreDifferentialFunctionals`, and
`Mathlib.LinearAlgebra.TensorProduct.Basis`. Existing public imports are unchanged.
The new module states the remaining geometric step: extending one cotangent functional
to the pulled-back differential sections, with its local differential formula.

## Proved and sorry left

One original theorem body is closed:
`AlgebraicGeometry.source_fibre_differential_injective_of_formula`
(node `lem-zl-source-fibre-differential-injective`). Its proof uses one newly stated
geometric lemma. This is a decomposition, not a net proof gain: one hole closed,
one hole added, net zero; zero of the two original obligations is fully discharged
without a new obligation.

The following two named holes remain in this delivery:

- `AlgebraicGeometry.exists_source_fibre_differential_formula`
  (`lem-zl-source-fibre-differential-formula`), unchanged in the item module.
- `AlgebraicGeometry.exists_source_fibre_differential_functional`
  (`lem-zl-source-fibre-differential-functionals`), the single new hole in
  `Sheaf.AlgebraicGeometry.SourceFibreDifferentialFunctionals`.

The two private algebraic helpers have complete proofs and no holes. The new lemma
contains no comparison map D and no injectivity conclusion; it concerns one scalar
functional and has no smoothness or finite-dimensionality hypothesis. Thus the
spanning argument, scalar-extension comparison and coordinate separation are actual
proved steps rather than a renamed original obligation. Empty T, zero cotangent
space, an empty basis and infinite-dimensional fibres are compatible with this route.

## No longer needed

No existing import or module is withdrawn. The injectivity proof no longer needs
`lem-ag-smooth-relative-differentials-finite-locally-free`: arbitrary vector-space
bases suffice. It also no longer directly uses
`lem-trf-relative-differential-sheaf-base-change` or
`lem-weil-pbc-module-stalk-pullback`; those remain geometric dependencies of the new
functional-extension lemma. All three original geometric dependencies remain needed
by the unchanged comparison-existence obligation. Consequently none is globally
pruned, and no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original injectivity plan said that agreement on differential generators and
finite-basis coordinates would prove injectivity. Agreement alone does not identify
the coordinates on the target; extending the individual coordinate functionals is
the geometric step needed to justify that calculation. This delivery states that
step explicitly, proves the remaining argument, and updates the injectivity node.
Smooth finite local freeness is unnecessary for this injectivity route.

No existing statement, definition, declaration visibility, or public import changes.
No shared consumer adaptation or change record is required.

## New nodes

`lem-zl-source-fibre-differential-functionals` is the extension of a single cotangent
functional, in `Sheaf.AlgebraicGeometry.SourceFibreDifferentialFunctionals`. Its node
records differential base change, normalized pullback, the stalk tensor comparison,
the stalk-skyscraper adjunction, and pullback of the structure sheaf. The docstring
gives the construction and its normalization on local differentials. This is the
geometric substep used by the proved separation argument, rather than an alternate
name for existence of D or injectivity of D. No change records are added.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
