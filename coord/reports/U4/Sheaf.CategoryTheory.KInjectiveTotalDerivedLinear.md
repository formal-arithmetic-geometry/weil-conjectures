## What changed

Filled the proof of
`CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions_linear` in
`Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear`, preserving every declaration
signature, definition, docstring and import.

The proof follows the existing five-step DAG plan. Mathlib supplies additivity
and scalar linearity of the homotopy-category functor and derived localization.
Naturality of the specified derived-functor unit gives the comparison formula
for arbitrary specified K-injective representatives. Every derived object has
such a representative by essential surjectivity and the hypothesis `enough`.
The K-injective Hom bijection provides lifts; their sums and scalar multiples
lift the corresponding derived maps. Cancellation of the comparison
isomorphisms proves additivity and scalar linearity. The same Hom bijection
provides existence and uniqueness in the final conjunct.

Sources checked: Stacks derived.tex, `lemma-K-injective` (070I),
`lemma-K-injective-defined` (070Y), and
`lemma-enough-K-injectives-implies` (070K). The proof imposes no exactness,
boundedness, monomorphic-resolution, or scalar-compatible-choice hypothesis.

Validation: `lcompile.py` compiled the module in 3.2 seconds, without errors or
warnings. Temporary `#print axioms` probes for both declarations reported only
`propext`, `Classical.choice`, and `Quot.sound`; the probes were then removed.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions_linear`
(blueprint: `lem-weil-kinjective-total-derived-linear`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
No statements were split off.

## No longer needed

None. All three existing imports and all declared proof dependencies remain
used. The existing DAG proof and unit route are unchanged; no node or module
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib already implements the homotopy and localization linearity and
K-injective Hom bijection required by the stated proof plan. The search result
for exact-functor derived linearity would add an unnecessary exactness
hypothesis and was not used.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
