## What changed

Proved `Algebra.smooth_of_localization_span_universes` with its signature unchanged.
Added proof-only imports of `Mathlib.RingTheory.Finiteness.FinitePresentationLocal` and
`Mathlib.RingTheory.Smooth.Locus`. Updated the node proof to the compiling argument.
Finite presentation descends from the spanning principal cover; the same cover lies
in the smooth locus, yielding formal smoothness. Together they give smoothness.
The argument is Mathlib's span criterion without its homogeneous RingHom wrapper.

## Proved and sorry left

Closed one hole: `Algebra.smooth_of_localization_span_universes`
(node `lem-weil-pbc-smooth-of-localization-span-universes`). No holes remain in this
module and none were added. The single-file compile passes without warnings.

## No longer needed

No imports or modules removed. The proof no longer uses
`def-weil-pbc-smooth-ring-map` as a proof dependency (it remains a statement dependency).
No additional statement modules or universe-transport intermediate theorems are needed.

## Where the brief, the DAG or earlier work was wrong

The homogeneous `RingHom.Smooth.ofLocalizationSpanTarget` cannot be applied directly
at distinct universes. Its ingredients already are universe-polymorphic:
`Algebra.FinitePresentation.of_span_eq_top_target`,
`Algebra.smoothLocus_eq_univ_iff`, and `Algebra.basicOpen_subset_smoothLocus_iff`.
Thus algebra-structure transport is unnecessary. The unit's realized statement and
steps are unchanged. Loogle found the finite-presentation criterion; LeanFinder found
the RingHom criterion and smooth-locus results; source grep and signature inspection
confirmed the different universe parameters. No new mathematical statement was added.

## Second reading by X3

1. I compared the delivered module with the repository version. The theorem signature is byte-for-byte unchanged; only the proof, proof-only imports, and explanatory docstring differ. The node's statement and interface are unchanged.
2. I compiled the module with `lcompile.py` and checked the theorem with `#print axioms`. It compiles without warnings and depends only on `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
3. The proof is mathematically valid: smoothness supplies formal smoothness and finite presentation of each localization; `FinitePresentation.of_span_eq_top_target` gives finite presentation of the target, while the smooth-locus cover criterion gives formal smoothness. The statement is unchanged and no new statement was added.
4. The proof uses the same localization-span route recorded by the node and preserves the unit's realized route. The old homogeneous `RingHom` wrapper is bypassed only because its universe-polymorphic component lemmas directly apply.
5. The node now records the actual proof steps and has empty `proof_deps`, matching the Lean proof. The public import remains needed for the statement; the two Mathlib imports are proof-only. No modules or imports were pruned.

I corrected the theorem docstring to describe the direct universe-polymorphic smooth-locus proof rather than claiming transported algebra structures. No declarations or statements were changed.
