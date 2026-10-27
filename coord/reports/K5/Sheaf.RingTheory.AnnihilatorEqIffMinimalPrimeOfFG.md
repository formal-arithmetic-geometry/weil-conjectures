## What changed

Proved `Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg` with its original signature.
The forward implication uses primality and `Ideal.minimalPrimes_eq_subsingleton_self`.
For the converse, the existing `Module.weakly_associated_atPrime_iff` gives a localized
annihilator whose radical is the extended prime. The proved private helper
`Ideal.exists_annihilator_eq_maximal_of_radical` turns this into an exact annihilator,
and `Module.exists_annihilator_eq_of_localization_atPrime` descends it.

The helper uses `Ideal.exists_pow_le_of_le_radical_of_fg` to choose the least n
with q^n contained in Ann(x). This n is positive. Choose r in q^(n-1) outside Ann(x).
Then r x is nonzero, q annihilates it, and its proper annihilator is contained in
the unique maximal ideal q, proving equality. This covers q = 0 as well: n = 1
and the same argument applies. A zero module cannot supply the proper radical
hypothesis; a zero ring cannot supply the prime hypothesis.

Added the private proof import `Mathlib.RingTheory.Finiteness.Ideal`. Both existing
Sheaf proof imports are used. Updated the node's finite-generator step and proof
origin to describe the least-ideal-power argument. Public imports, statements,
and existing docstrings are unchanged. No other modules or interfaces changed.

## Proved and sorry left

Closed 1 hole: `Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`
(node `lem-sc-ass-weakass-fg-prime`). The private helper is fully proved.
There are zero remaining holes in the item and zero holes added or split off.

The proof uses the existing stated dependencies
`Module.weakly_associated_atPrime_iff` (`lem-sc-weakass-localization`) and
`Module.exists_annihilator_eq_of_localization_atPrime`
(`lem-sc-associated-localization-fg`). Their existing holes are unchanged and
remain separate items; this delivery proves the assigned theorem from them.

## No longer needed

None. Both declared proof dependencies and both Sheaf imports remain necessary.
No imports, nodes, modules, or unit steps were pruned. The exponent-sum minimization
is replaced by least-ideal-power minimization within the same localization route.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or the planned route. The middle
step admits a shorter implementation using Mathlib's finite-generation/power lemma,
so no separate statement or new node is needed. The unit's route is preserved.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
