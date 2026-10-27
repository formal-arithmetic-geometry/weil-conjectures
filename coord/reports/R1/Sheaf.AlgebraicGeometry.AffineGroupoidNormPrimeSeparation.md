## What changed

Proved `AlgebraicGeometry.affineGroupoid_norm_prime_separation` without changing its signature,
using proved private helpers for kernel uniqueness, finite-algebra residue fields, primes over
geometric points, and local norm charts. The source fibre is treated directly as a finite
algebra. Tensor universality constructs the stated equivalence with its exact evaluation
condition. Prime avoidance constructs f. The existing finite free norm nonvanishing theorem
then proves both evaluations of g, using the identity arrow for its zero value.

Added proof imports of `Mathlib.RingTheory.Artinian.Module`,
`Mathlib.RingTheory.TensorProduct.Finite`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatNorm`. Updated the item's node proof
and proof dependencies to describe this argument. No public interface or other module changed.

Validation: the complete proof compiled through lcompile.py in 10.2 seconds with no warnings.
The final delivery repeats compilation and checks the axioms of all delivered declarations.
The theorem statement is byte-identical to the original. The new norm import adds five
non-Mathlib modules relative to the original item import closure, all with zero textual holes.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.affineGroupoid_norm_prime_separation`
(node `lem-a1-affine-groupoid-norm-prime-separation`). Holes closed: 1; holes added: 0;
holes left: 0. No statements were split off. Every private helper has a complete proof.

## No longer needed

Removed the proof imports `Mathlib.AlgebraicGeometry.Morphisms.Proper` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`. Also removed the unused direct import
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` and the redundant direct import
`WeilConjectures.Mathlib.RingTheory.Localization.NormTrace`; the latter criterion remains
used through the public geometric norm API.

The following planned dependencies are unnecessary for this proof:

- `lem-weil-pbc-fibre-product-affine-spectra`: work directly in the tensor algebra.
- `lem-weil-pbc-finite-morphism-permanence`: module base change supplies finiteness.
- `lem-weil-pbc-finite-closed-map-finite-fibres`: Artinian spectrum finiteness suffices.
- `lem-weil-pbc-finite-dimensional-domain-is-field`: the Mathlib Artinian prime-maximal
  instance and the integral algebraically closed field theorem supply the required facts.

These are pruned from this node's proof dependencies; no source declaration or module is
withdrawn, and no global unreachability is claimed. The unit's realization lists are empty
for this item, and its statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned scheme-fibre argument is longer than necessary:
Mathlib already proves finite-module base change and finiteness of an Artinian prime spectrum.
The existing `AlgebraicGeometry.mem_basicOpen_normAt_of_free` also provides the geometric
norm criterion needed on the supplied charts.

Searches used leanfinder, loogle and grep through msearch.py, plus direct searches of Mathlib,
Sheaf and WeilConjectures. No theorem covering the entire statement was found. The useful
existing result was the finite free norm criterion, which is reused rather than restated.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
