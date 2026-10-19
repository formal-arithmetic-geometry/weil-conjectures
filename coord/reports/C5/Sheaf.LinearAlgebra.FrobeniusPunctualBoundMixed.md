## What changed

Filled the proof of
`FrobeniusModule.isMixedOfWeightsAtMost_of_forall_hasEigenvalue` in
`Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed` by strong induction on dimension.
The full eigenspace of a nonzero eigenvalue is a pure stable submodule. Its quotient has
smaller dimension and inherits the eigenvalue bound by the proved upstream
`FrobeniusModule.hasEigenvalue_of_surjective`. The existing
`FrobeniusModule.IsMixedOfWeightsAtMost.of_shortExact` assembles the two mixed modules.
The proved private helper `mixed_of_pure` constructs the two-term filtration, including
the zero-dimensional case. Logarithms give the eigenspace's real weight and its upper bound.

The node's proof, proof dependencies and proof origin record this dimension-induction route.
Only proof imports changed; no existing statement, definition or public import changed.
The resumed session repaired the preserved attempt's coercions and Mathlib API names.
Validation: `lcompile.py` compiled the complete module cleanly in 3.9 seconds, exit 0.
The delivery dry run also checks the declarations and their axioms before pushing.

## Proved and sorry left

Original hole: `FrobeniusModule.isMixedOfWeightsAtMost_of_forall_hasEigenvalue`
(node `lem-a1-punctual-bound-module-mixed`). Its sandbox proof has no remaining `sorry`.
Holes added: zero. Split-off statements: zero. No `sorry` remains in the delivered module.
One original hole is closed by a complete compiling proof from the existing declarations.
No new proof obligation is introduced by this delivery.

The imported, existing
`FrobeniusModule.IsMixedOfWeightsAtMost.of_shortExact`
(node `lem-a1-extension-bounds`) remains the separate dependency's proof obligation;
this delivery neither creates nor modifies that theorem.

## No longer needed

Removed `import Sheaf.LinearAlgebra.SpectrumExactSequence`; the proof does not need
`FrobeniusModule.spectrum_exact_sequence`, node `lem-a1-spectrum-exact-sequence`.
Only eigenvalue membership for a quotient is needed, supplied by the already proved
`FrobeniusModule.hasEigenvalue_of_surjective` in
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map`. The node's proof dependencies
therefore omit `lem-a1-spectrum-exact-sequence`.

The preserved attempt's broader
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact` import is replaced by `Map`.
No Jordan–Holder filtration theorem, simple-factor dimension lemma, multiplicity formula,
or characteristic-polynomial factorization is needed. No modules are withdrawn and no
unit statement or realized proof step is bypassed (the item's unit record has no realized
node attached to this lemma).

## Where the brief, the DAG or earlier work was wrong

The upstream `hasWeightsAtMost_of_forall_hasEigenvalue` proves the eigenvalue-bound
predicate, rather than the finite stable pure-filtration predicate required here.
It therefore cannot close this item. The explicit eigenspace argument constructs
that filtration via the existing extension theorem without changing the conclusion.

The original plan's full spectrum theorem is stronger than the quotient membership
needed by dimension induction. The zero space is handled by a two-term filtration
with a zero pure graded piece; positivity of the eigenvalue norm is used only in the
nonzero branch. For nonsemisimple Frobenius the eigenspace can be proper; quotient
dimension still decreases, so the proof does not assume a stable complement.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
