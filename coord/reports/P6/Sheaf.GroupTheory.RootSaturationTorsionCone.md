## What changed

Proved `AddCommGroup.root_saturation_torsion_cone` in
`Sheaf.GroupTheory.RootSaturationTorsionCone`, preserving its complete statement.
Three proved private helpers supply a positive common denominator, the cone criterion for
an additive map with torsion kernel, and tensor injectivity detected by basis coordinates.
Mathlib supplies finiteness of the torsion submodule and a finite basis of the torsion-free
quotient. Tensor symmetry lets the cone calculation use the rational module structure on
`ℚ ⊗[ℤ] L`. Private imports of `Mathlib.LinearAlgebra.TensorProduct.Associator`
and `Mathlib.Algebra.Order.Field.Rat` supply tensor maps/symmetry and rational inequalities.
The node proof now records this implementation.

## Proved and sorry left

Closed the sole hole, `AddCommGroup.root_saturation_torsion_cone`
(node `lem-trf-root-saturation-torsion-cone`). Added zero holes; none remain.
The private helpers `common_denominator`, `cone_criterion`, and
`tensor_one_injective` are completely proved. No split-off statements or axioms were added.

## No longer needed

The proof avoids explicitly constructing the free/finite product decomposition of G,
its quotient equivalence, and the full rational tensor coordinate isomorphism. It uses
Mathlib's proved finite-torsion corollary of the PID structure theorem and the existing
`lem-trf-fg-torsionfree-group-free` Mathlib leaf instead. The original structure-theorem
node remains relevant through its torsion corollary; the free-module and tensor-product
definition nodes remain used. No original import was removed, and no existing Sheaf module or route node is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original coordinate proof was valid but more
elaborate than necessary: individual tensor coordinate maps already prove injectivity.
The common denominator is the product of all denominators, including product 1 for the
empty list; killing the residual torsion handles finite groups and rank zero uniformly.
The unit route and all public declarations and public imports are unchanged.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
