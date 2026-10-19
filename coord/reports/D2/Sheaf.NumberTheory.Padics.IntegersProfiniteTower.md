## What changed

Proved `Padic.coefficientExtension_integers_profinite_tower` without changing its statement or
its three definitions. Added the proved helper module `Sheaf.NumberTheory.Padics.IntegersCosetBasis`.
It computes each positive reduction fibre as a closed metric ball and derives its neighbourhood
basis from geometric decay of the uniformizer norm. The main proof constructs the compatible
reduction ring homomorphism and proves injectivity from that basis. Compactness of the closed
unit ball and the nested closed coordinate fibres prove surjectivity. The compact-to-Hausdorff
criterion gives the homeomorphism. Locally constant reductions separate preconnected subsets,
proving total disconnectedness. A finite subcover of locally constant fibres gives a common
exponent for finite-valued continuous maps; quotient surjectivity proves unique factorization
at every higher exponent.

## Proved and sorry left

Closed the original hole in `Padic.coefficientExtension_integers_profinite_tower`
(node `lem-sfb-integers-profinite-tower`). The added theorem
`Padic.coefficientExtension_integers_coset_basis` (node `lem-sfb-integers-coset-basis`)
is also proved. No holes remain in either module; no holes were added. This is a proof,
not a decomposition into unproved intermediate assertions.

## No longer needed

Removed the unused proof import `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
The proof no longer uses `lem-weil-l-adic-extension-complete`: compact nested closed fibres
replace Cauchy representatives. It does not use `lem-weil-valued-dvr-finite-quotients`:
quotient surjectivity is generic and discreteness suffices for the topological arguments.
It does not use `lem-weil-l-adic-extension-absolute-value` separately: the spectral norm and
the DVR membership criterion give the closed-ball computation. No unit statement or unit
proof step is bypassed. The original public finite-coefficient import is retained to preserve
its exported interface; the proof itself does not invoke its finiteness theorem.

## Where the brief, the DAG or earlier work was wrong

The planned Cauchy-sequence reconstruction is unnecessary once properness has made the integer
ring compact. The final factorization argument in fact works for any discrete codomain and
uses neither its finiteness nor surjectivity of the given function. The original statement,
including those hypotheses, is unchanged. Edge cases checked: the first positive quotient,
zero differences in the ideal calculation, ramified uniformizer norms, singleton codomains,
and the empty codomain (which has no map from the nonempty integer ring).

## New nodes

`lem-sfb-integers-coset-basis` records the proved neighbourhood-basis lemma, exactly parent
proof step 1. Its module is `Sheaf.NumberTheory.Padics.IntegersCosetBasis`; it has no `sorry`.
The proof uses the DVR theorem as the same arithmetic tool already approved for the parent.
No definition or statement was changed, so no change record or consumer adaptation is needed.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
