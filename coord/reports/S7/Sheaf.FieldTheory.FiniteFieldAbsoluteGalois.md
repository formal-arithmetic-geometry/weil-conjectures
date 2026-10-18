## What changed

Proved `finiteField_absoluteGaloisGroup` in
`lean/Sheaf/FieldTheory/FiniteFieldAbsoluteGalois.lean`, with its original signature unchanged.
The finite root field construction uses the already proved
`FiniteField.exists_unique_subfield_of_closure`; cardinality gives degree and degree uniqueness.
Mathlib gives the finite Galois extension, the Frobenius order, and its power bijection.

Three proved private helpers supply equality on a dense generator, the coordinatewise
completion isomorphism, and density of Frobenius powers. The density proof uses the proved
`FiniteField.frobeniusAlgEquivOfAlgebraic_apply_eq_self_iff` and Mathlib infinite Galois
correspondence. Each completion coordinate is constructed through a finite root field of the
order of the image of 1 in the cyclic quotient. Compatibility follows from density;
compactness proves surjectivity, and finite open normal quotients prove injectivity.
All choices in the completion helper are of continuous homomorphisms uniquely determined by
their value on the dense generator. No data is chosen from an unproved existence theorem.

Added proof-only imports `Mathlib.FieldTheory.Galois.Infinite` and
`WeilConjectures.Mathlib.FieldTheory.Finite.Basic`. Updated the existing node's proof,
proof dependencies and proof origin to match this route. The unit's finite-extension and
absolute-Galois conclusions are preserved. No other module or existing declaration changed. The public-import removal is recorded in
`coord/changes/finite-field-absolute-galois-proof-imports.md`, including the sole consumer.

Validation: the complete file compiled through `lcompile.py` with no errors or warnings.
The n=1 case uses the trivial quotient (whose identity has order 1); the proof works in
independent universes for K and Ks. Positive finite degree explicitly supplies
finite-dimensionality before cardinality is used, so infinite-dimensional fields with
finrank 0 cannot enter the uniqueness argument. The delivery tool checks all declaration
axioms and the unchanged signature.

## Proved and sorry left

Closed the sole original hole: `finiteField_absoluteGaloisGroup`
(node `det-base-field-cd-galois-group`). Proved 1 of 1 sorries. Added 0 holes and split off 0.
There are no sorries left in the delivered module or in new modules (none).
All three private helpers are fully proved. This is a proof, not a decomposition.

## No longer needed

Removed the unused public import `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`.
Its `IsSepClosure.exists_intermediateField_mem` is unnecessary: the finite fields come from
the root-subfield construction, and density and finite quotient separation replace an
explicit union of finite subextensions. Mathlib's `IsSepClosure` remains publicly imported.
The sole direct consumer `Sheaf.Paper.RealBoundaryPathIndependence` uses none of the removed
module's declarations in its signatures or definitions; its public imports also reach the
existing IsSepClosed module. The public theorem's signature and mathematical meaning stay
identical.

Removed `def-pd-separable-closure` from proof_deps only; it remains a statement dependency.
Its separate compositum/finite-subextension membership theorem is not used by this proof.
The planned classification of field inclusion by divisibility, classification of subgroups
of Z as nZ, and reindexing the Galois limit by positive integers are unnecessary. No other
existing node or module can be pruned by this delivery: the finite-root-field construction,
finite Frobenius facts, algebraic-closure specialization, and Krull-limit compactness are
all retained. No Lean modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan asked for more indexing machinery than
needed: directly constructing coordinates for all finite quotients of Z proves the same
profinite-group assertion and the image-of-Frobenius clause. The source unit's argument
through finite cyclic Frobenius quotients is retained. The unique-subfield dependency is
already proved, so the resulting theorem need not rest on any project sorry.

Two compile requests temporarily received no answer from the compile server; subsequent
requests completed successfully. These were server no-response timeouts, not Lean file
timeouts. No tool, repository file, target signature, or public definition was modified.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
