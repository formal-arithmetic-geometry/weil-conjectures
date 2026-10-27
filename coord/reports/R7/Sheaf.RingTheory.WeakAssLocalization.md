## What changed

Proved `Module.weakly_associated_atPrime_iff` in
`Sheaf.RingTheory.WeakAssLocalization`, with its existing signature and public imports unchanged.
Added the private proof import `Mathlib.RingTheory.Ideal.MinimalPrime.Localization`.
The proved private helper `Module.colon_localized_mk` identifies the annihilator of `m/s`
with the extension of the annihilator of `m` by clearing denominators.
`IsLocalization.minimalPrimes_map` then proves the first equivalence by contraction, and
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes` supplies the radical formula.
The reverse radical implication uses invariance of minimal primes under taking radicals.
Updated the existing node's proof and proof_origin to describe this assembly explicitly;
its proof dependencies and source are unchanged. No new public declarations or definitions.

LeanFinder search found associated-prime results with stronger hypotheses, not this theorem.
Loogle and Mathlib grep located the exact minimal-prime localization formula used here.
The unit `sk-def-av-ample-degree` has no realized steps; its route is preserved.
The general denominator calculation also covers zero elements and zero modules: their
annihilator is the top ideal, with no minimal primes, so no nonzero assumption is introduced.

Validation: the module compiled cleanly through `lcompile.py` (5.4 seconds).
Delivery preflight also checks compilation and axioms of every added declaration.

## Proved and sorry left

Closed: `Module.weakly_associated_atPrime_iff`
(node `lem-sc-weakass-localization`), the module's only original hole.
Proved private helper: `Module.colon_localized_mk`.
Original holes: 1. Closed: 1. Added: 0. Remaining: 0. Split off: 0.
No declaration in this delivery contains `sorry`.

## No longer needed

None. No imports, nodes or modules were removed. The existing proof dependency
`lem-weil-pbc-primes-of-localization` remains needed through Mathlib's localization formulas.
No unfinished Sheaf dependency was imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. Mathlib already contains the minimal-prime correspondence
and radical formula; the proof implements the planned annihilator argument and uses those
existing results rather than rebuilding prime correspondence. The node proof now records
these exact Lean ingredients and the order of the implications.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
