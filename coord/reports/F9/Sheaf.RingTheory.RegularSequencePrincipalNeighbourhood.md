## What changed

Proved `RingTheory.exists_isRegular_localizationAway_of_isRegular_localizationAtPrime`
in `Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood`, with its signature and public
imports unchanged. The proof follows Stacks Tag 061L using the inverse image colon ideal
`(I : x)` of each kernel. Finite generators give a common denominator outside the prime.
Two proved private helpers clear denominators and establish regularity on a localized
quotient. The main proof takes the finite product and proves properness of the final ideal
by disjointness from the denominator monoid, including the empty sequence.

Replaced the proof import `Mathlib.Algebra.Module.LocalizedModule.Exact` with
`Mathlib.RingTheory.Localization.Ideal`. Updated the theorem docstring and the existing
DAG node's proof, proof dependencies, and proof origin to match this argument.
No definition or statement changed; no consumer adaptation is required.

## Proved and sorry left

Closed the sole original hole:
`RingTheory.exists_isRegular_localizationAway_of_isRegular_localizationAtPrime`
(node `lem-exc-regular-sequence-principal-neighbourhood`).

Holes closed: 1. Holes added: 0. Holes left in the item or added modules: 0.
The private helpers `exists_mul_mem_of_regular_atPrime` and `regular_away_of_mul_mem`
are proved in full. No split-offs or new modules.

## No longer needed

Removed direct proof import `Mathlib.Algebra.Module.LocalizedModule.Exact`.
Removed proof dependencies `lem-weil-pbc-localization-module-exact` and
`def-weil-pbc-module-localization`: the inverse-image ideals and the ring-localization
membership criteria avoid constructing localized kernel and quotient modules.
These removals concern this proof only; other project consumers can still need them.
All original statement dependencies and the Noetherian finite-submodule dependency remain.
No Sheaf or WeilConjectures modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The six-step source argument can be implemented
more directly in the ring case with colon ideals, without the original module-localization
comparison. The unit's realized statement and steps are unaffected (its realization arrays
are empty for this supporting node).

Searches through leanfinder, loogle, logged Mathlib grep, and local source ripgrep found
preservation of regular sequences under localization and module support lemmas, but no
existing theorem spreading this regular sequence to a principal neighbourhood.
The source read was `literature/stacks-project/algebra.tex`,
`lemma-regular-sequence-in-neighbourhood`, Tag 061L.

The retained proof was rechecked against the current source and compiled on the
project server. Repaired the sole diagnostic, a trailing blank line in its docstring.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
