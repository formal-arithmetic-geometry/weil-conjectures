## What changed

Proved `SheafOfModules.derivedTensorAssociator_exists` for every resolving
presentation quantified over by the original statement.

A proved private descent lemma constructs the left and right iterated
representative comparisons, conjugates the complex associator by them, and
applies the existing ternary extension theorem. Cancellation verifies its
representative square. The unsigned triple-summand formula determines the
complex associator uniquely; cancellation and ternary faithfulness then prove
uniqueness of the derived normalization.

The private total-associator descent proof uses Mathlib's native complex
associator with the gradewise tensor-existence and triple-preservation
instances already available for the module-sheaf category.
Its summand formula follows from `ι_mapBifunctorAssociatorX_hom` and the two
triple-inclusion equations. Triple-total extensionality proves uniqueness.
Graded associator naturality and the comparison of the raw tensor-map functor
with `tensorHom` establish naturality. Tensor closure, ternary extension and
faithfulness come from the already imported
`Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`.

The proof uses the module's original imports. No new global instance or
transparency attribute is exported.

All existing declaration signatures, definition bodies, public imports and
other theorem proofs are preserved. No target statement changes. The existing
node's proof and proof origin describe the implemented associator argument.
The complete delivered source compiled without warnings in 54.7 seconds with
`lcompile.py` before delivery.

## Proved and sorry left

Closed one of the three original holes:
`SheafOfModules.derivedTensorAssociator_exists`.
No holes added; no statements split off.

Two original named theorem holes remain:

- `SheafOfModules.shiftedTensorMorphismCalculus_local`.
- `SheafOfModules.shiftedTensorMorphismCalculus`.

Both remain attached to `lem-pur-shifted-tensor-morphism-calculus`, with their
original statements and natural-language proofs. No definition contains a hole.

## No longer needed

None: no original import, module or DAG dependency is removed. The new
associator proof needs the additive-constraints module and Mathlib's native
complex API. The signed total-coherence node remains needed by the unfinished
local calculus, and the exact pullback comparison node remains needed by the
unfinished full calculus. No unit statement, unit step or adopted source
declaration is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The associator existence hole can
be closed from the existing tensor-closure, ternary-extension and uniqueness
lemmas, without assuming coherence of the arbitrary tensor presentation.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
