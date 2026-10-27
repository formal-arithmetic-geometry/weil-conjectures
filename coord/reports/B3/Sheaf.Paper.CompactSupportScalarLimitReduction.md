## What changed

Proved `WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization` without changing its
statement or any existing definition. Coordinate extensionality identifies the chosen
`scalarRoosTensor` with the existing canonical `roosAdditiveComparison`. Its augmentation
formula proves the strict augmentation equation, including the zero shifted coordinate.
The derived equation follows from the new, fully proved abstract theorem
`CategoryTheory.RoosTensor.roosTensorNormalization` in
`Sheaf.CategoryTheory.RoosTensorNormalization`.

The abstract proof compares the ordinary-limit inclusions, checks the degreewise
limit-preservation comparison using each projection, proves the full unit equation of the
canonical three-factor derived comparison, and cancels the localized Roos inclusion on
K-injectives. Naturality along a K-injective resolution extends the equation to every complex.
The private unit-normalization calculation reuses the proved argument already present in
`ScalarLimitTensorComposition`; that consumer is neither imported nor modified. Two proved
private coordinate helpers keep the concrete scalar specialization small, avoiding repeated
elaboration of its sheaf functors. They are available only through the proof import.

A private unit-equation lemma allows the chosen Roos comparison to remain locally
irreducible during subsequent proofs. The local reducibility settings do not change
the exported definitions or the behavior seen by importers.

All existing public imports and declarations are preserved. The new proof imports do not
change the item module's public interface. Only the item's Lean file, its node, the new
proved helper module and its node are delivered. No other existing module is adapted.

Validation: the final `lcompile.py --all` request compiled both delivered Lean modules
successfully, with no diagnostics and with the server's per-file time-limit checks passing.
All temporary profiling options were removed before this successful compile.

## Proved and sorry left

Closed 1 of the item's 2 original holes:
`WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization`
(node `lem-pur-compact-support-scalar-limit-reduction`).

The one remaining original hole is
`WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`
(node `lem-pur-compact-support-scalar-limit-reduction`), whose statement and proof placeholder
are unchanged. The new helper theorem is completely proved. Added holes: zero. Split-off
holes: zero. This delivery proves the tensor-normalization helper; it does not claim to
complete the compact-support assembly or close all transitive dependencies.

Edge cases: no positivity, nonzero-object or nonempty-site hypothesis is introduced.
The abstract theorem needs no invertibility of a product comparison. Zero complexes and
zero additive functors satisfy its equations. Its tower-limit preservation and exactness
hypotheses supply precisely the canonical derived-composite factors; they are existing
proved properties of the finite-free scalar functor used in the item.

## No longer needed

No existing dependency, declaration or import is withdrawn. The seven-step compact-support
route and its existing dependencies are retained for the remaining original theorem.
The proof uses the existing additive Roos comparison and augmentation calculation rather
than constructing another cone map. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The rework table records an earlier quarantine caused by a false-tail import. The current
item source is present with its established Lean attachment and two original theorem holes.
This delivery preserves that source and its dependencies, and does not treat the old
quarantine entry as permission to delete or withdraw the module.

The source Tag 0941 supplies the ordinary-limit/Roos construction. It does not state the
entire normalized scalar comparison; the abstract derived-unit calculation is explicitly
recorded as agent-written. No target statement, definition, or adopted-source declaration
is changed.

## New nodes

`lem-pur-roos-tensor-normalization` records the fully proved abstract equality between
the canonical derived tensor/limit comparison and the localization of the canonical strict
additive Roos map. Its source is Tag 0941 and parent Step 4; its statement, proof steps,
searches and edge cases match the new Lean theorem. It is a general categorical step of
the argument and introduces no new assumption or `sorry`. No change record is required:
no existing shared interface is modified.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
