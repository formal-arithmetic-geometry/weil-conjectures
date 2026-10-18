## What changed

Proved `DerivedCategory.isPerfect_and_tensor_homology_vanish_of_maximal_fibres` with its
original signature. The proof computes derived tensors using the bounded-above finite-free
model, establishes the entire Tor interval, and applies the already proved
`DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude`.

Added the proved single-degree theorem
`CochainComplex.isZero_homology_tensor_of_residue` in
`Sheaf.Algebra.Homology.FreeComplexResidueTensorExact`. Its four private, proved helpers
compare restricted scalar extension with ordinary tensor, transfer quotient residue
exactness to the fraction-field convention, preserve cancellation under arbitrary tensor,
and descend exactness along a principal cover. No definition or existing signature changes. Both delivered files compile without errors
or warnings (4.7 and 3.6 seconds). The original downstream module
`Sheaf.RingTheory.RlimPerfectComplete` also compiles unchanged against these outputs
(5.0 seconds). The delivery tool independently checks compilation and axioms.

The source read was Stacks `more-algebra.tex`, the direct matrix proof of Tag 068U
(`lemma-cut-complex-in-two`) and implication (3) to (1) in Tag 068V
(`lemma-check-perfect-pointwise`). The unit's realized statements and steps are unaffected.

## Proved and sorry left

Closed one existing hole:
`DerivedCategory.isPerfect_and_tensor_homology_vanish_of_maximal_fibres`
(node `lem-weil-pbc-pseudocoherent-maximal-fibre-perfect`).

Added zero holes. The new single-degree theorem and all its private helpers are proved.
No `sorry` remains in either delivered module. The proof uses the existing stated
`CochainComplex.exists_localized_homotopyEquiv_zero_degree`, whose existing hole remains
in its own, unchanged module; it is not a hole introduced by this delivery.

## No longer needed

The new proof avoids both local interval cuts and gluing perfect local models. It obtains
universal tensor exactness degree by degree directly from the cancellation homotopies,
then invokes the already proved pseudo-coherent finite-Tor criterion.

Removed imports from the item:
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`
- `Mathlib.RingTheory.LocalProperties.Exactness`
- `Mathlib.RingTheory.Ideal.Maximal`
- `Sheaf.Algebra.Homology.FreeComplexResidueDegreeCancellation`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
- `Sheaf.RingTheory.PerfectPrincipalCoverGlue`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`

The cancellation and maximal-ideal tools remain needed through the new chain-level lemma.
The generic bounded-above K-flatness API is provided by the retained `FlatModel` import.

Obsolete direct proof dependencies:
- `lem-pur-derived-change-of-rings`: no derived scalar-extension functor is constructed.
- `lem-weil-pbc-perfect-ring-principal-cover-glue`: replaced by the already proved finite-Tor
  criterion; this module and its auxiliary local-perfect gluing work are not used here.
- `lem-pc-module-bounded-flat-kflat`: its proved generic K-flatness input is applied directly.
- `lem-weil-pbc-linear-map-bijective-at-maximal-localizations`: direct principal-cover
  exactness detection replaces this particular zero-map criterion.

The obsolete top-level tool approvals for `lem-pc-module-bounded-flat-kflat` and
`lem-pur-derived-change-of-rings` are removed from this node. The original statement
dependencies and all target signatures remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's two cuts and finite principal perfectness-gluing argument are unnecessary.
A residue-exact degree can already be canceled locally up to chain homotopy; tensoring
with any module preserves the homotopy equations, so the same degree vanishes universally.
Applying the existing, proved finite-Tor criterion is shorter than constructing local
models with exactly the prescribed support and then gluing perfectness.

The original imports did not directly provide the existing single-module K-flat tensor
comparison in their docstring; `QObjTensorSingleFunctorObjIso` is the more precise API.
No statement was disputed or repaired.

## New nodes

`lem-weil-pbc-free-complex-residue-tensor-exact` records the proved single-degree universal
exactness result, strictly below the item and without pseudo-coherence, interval bounds,
perfectness, or a derived-category hypothesis. Source: Tags 068U and 068V. LeanSearch,
LeanFinder, and Mathlib/source/DAG text searches found tensor exactness and faithfully-flat
criteria, but no duplicate of this residue criterion. The zero ring, an empty principal
cover, a zero middle term, an unbounded complex, and arbitrary nonflat test modules are
covered by the proof. The public-import pruning is recorded in
`coord/changes/C1-maximal-fibre-import-pruning.md`; the sole downstream consumer
already imports the removed dependency directly and compiled unchanged.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
