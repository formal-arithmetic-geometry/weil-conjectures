## What changed

Proved `Module.associated_prime_localize_at_prime` in
`Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime` without changing its signature or
visibility. For each witness, compute the contraction of the localized annihilator
using `LocalizedModule.mem_ker_mkLinearMap_iff` and primality. Recover the annihilator
with `IsLocalization.map_under`, then use the original witness and
`Ideal.isPrime_map_of_isLocalizationAtPrime` to establish association.

Updated the declaration's proof docstring and the existing node's `proof`,
`proof_deps`, and `proof_origin` to describe this direct argument. Imports are
unchanged: all three public imports serve the statement. No definitions, statements,
new declarations, or other modules changed.

## Proved and sorry left

Closed the only hole: `Module.associated_prime_localize_at_prime`
(node `lem-weil-pbc-associated-prime-localize-at-prime`). One of one sorries proved;
zero split off; zero holes added; no sorries remain in the delivered module.
Single-file compilation passed without warnings. The delivery dry run checks axioms.

## No longer needed

The proof no longer needs node `lem-weil-pbc-localization-module-exact`, whose
Mathlib declaration is `LocalizedModule.map_exact` in
`Mathlib.Algebra.Module.LocalizedModule.Exact`. Its proof-only dependency is removed
from this item's DAG route; that module was not imported in the original item, so
no Lean import was removed. The quotient construction and localized injection of
the previous proof steps 1–2 are unnecessary. This pruning is local to this item;
other users of the exactness node may still need it.

Both localization definition nodes remain used. The annihilator-associated-prime
definition and all three original imports remain needed. No unit statement or
realized unit step is bypassed: this item is below the realized nodes of `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

The old argument is mathematically valid, but its quotient-injection and exactness
steps are unnecessary: direct contraction of the annihilator proves the stronger
witness equality with the existing Mathlib fraction kernel criterion and ideal
correspondence. The existing signature correctly handles arbitrary commutative
rings and modules, with no Noetherian hypothesis. No statement correction was needed.

## Second reading by T2

1. Compared the delivered Lean file and existing node against the repository.
   The theorem signature is byte-for-byte identical, and its visibility, imports,
   definitions and statement dependencies are unchanged. Only the proof, its
   explanatory docstring and the permitted node proof fields changed. Pass.
2. Compiled the delivered file locally without errors or warnings. A scratch
   copy with `#print axioms Module.associated_prime_localize_at_prime` reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no sorries,
   forbidden declarations, new definitions or arbitrary witness constructions.
   Read both directions of the contraction equality and the final association
   witness, including their equality orientations. Pass.
3. No statements were split off and no new declarations or nodes were added.
   Checked edge cases: a zero module or zero ring admits no associated prime
   hypothesis; over a field the zero prime and a nonzero witness give the same
   annihilator calculation. No Noetherian assumption is used. Pass.
4. Searched the upstream library and Sheaf ring-theory modules, and read Mathlib's
   associated-prime localization results and localized-module kernel criterion.
   Mathlib's association uses radical annihilators, so its association theorem
   does not supply this exact witness equality for arbitrary rings. The direct
   kernel/contraction proof uses existing Mathlib facts and is suitably short.
   Each public import supplies statement data: annihilator association, ring
   localization at a prime, or module localization at a prime. The report lists
   the sole removed proof dependency, localization exactness. Checked
   `dag/units/sk-thm-p1.json`: neither this item nor the removed exactness node
   is a realized unit statement or step, and the unit route is preserved. Pass.
5. The three node proof steps match the contraction calculation, ideal
   correspondence and association witness in Lean. Their dependency union is
   precisely the updated `proof_deps`; the origin records the direct
   formalization of the source's annihilator equality. Unrelated node fields
   and the node's statement are unchanged. No new-node fields are required. Pass.

Second reading changed only this report: no proof or metadata repair was needed.
The independent checks confirm one hole closed, zero holes added, and no
remaining local or transitive proof holes in this theorem.
