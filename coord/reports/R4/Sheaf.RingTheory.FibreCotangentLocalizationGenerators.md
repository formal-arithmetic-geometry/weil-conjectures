## What changed

Filled `KaehlerDifferential.FibreLocalization.comparison` in
`Sheaf.RingTheory.FibreCotangentLocalizationGenerators`. Constructed the extension
rho by the localization universal property after checking its denominators through
the kernel of the fibre residue map. Composed Mathlib's localization-tensor
equivalence, two tensor cancellations, differential base change, and tensor
symmetry with the prescribed transported scalar actions. Verified the forward
fraction formula, inverse pure-tensor formula, spanning clause, finite
dimensionality and dimension bound. The theorem and all definitions keep their
original signatures and bodies, apart from the theorem proof.

A proved private wrapper `scalarCancel` specializes the existing Mathlib
cancellation equivalence while keeping its scalar-instance synthesis generic.
It adds no mathematical assumption or public interface.

Added the proof import `Mathlib.RingTheory.Localization.BaseChange` and updated
the item's proof steps and dependencies to reflect the actual composition.
The complete module compiled through `lcompile.py` in 23.0 seconds with no
warnings or errors.

## Proved and sorry left

Closed the sole original hole:
`KaehlerDifferential.FibreLocalization.comparison`
(node `lem-trf-fibre-cotangent-localization-generators`).
Holes closed: 1. Holes added: 0. Holes left in the delivery: 0.
No decomposition and no split-off statements.

## No longer needed

Removed the proof import `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`.
The direct finite spanning-family dimension bound avoids separately applying
`lem-weil-span-independent-subfamily` and
`lem-weil-dimension-span-independent-family`; both have been removed from this
node's proof dependencies. They are Mathlib leaves, so no project Lean module
is withdrawn. The remaining original proof dependencies are used.
The existing Mathlib leaf `lem-trf-scalar-tensor-cancel-base-change` records the
cancellation equivalence used in place of constructing balanced maps by hand.
No source-library declarations or modules are removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The original plan was longer than
necessary: Mathlib already constructs localization-tensor comparison and tensor
cancellation with the needed fraction formulas. Its direct spanning-family
finrank bound also removes the independent-subfamily detour. No unit route or
target statement is changed. The proof covers the empty generating family and
arbitrary prime ideals without finiteness or flatness hypotheses on A over R.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
