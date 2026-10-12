## What changed

Replaced the sorry in `exists_mem_maximalIdeal_smul_injective` with a complete proof.
Added proof-only imports `Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness` and
`Mathlib.RingTheory.Regular.IsSMulRegular`. The signature and public imports are unchanged.
The proof combines finiteness, prime avoidance, and the characterization of regular
scalars, then uses maximality to contradict the hypothesis. It implements the existing
DAG route by contradiction, including the empty-associated-primes case.

## Proved and sorry left

Closed: `exists_mem_maximalIdeal_smul_injective`
(node `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated`), the sole original hole.
No holes remain in the item; no holes were added or split off.
Single-file compilation passed. Axiom inspection reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

None. No imports were removed. All three existing proof-dependency nodes remain needed:
`lem-weil-pbc-noetherian-associated-primes-finite`, `lem-weil-pbc-prime-avoidance`, and
`lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes`. They are Mathlib
leaves and introduce no project modules or holes.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The three DAG dependencies have `mathlib_match`
records rather than project `lean` declarations; their Mathlib results suffice directly.
The unit record confirms this auxiliary node does not replace a unit statement or step.
The checkout lacks `literature/blueprint/`, and `coord/delivery-errors.md` has no section I;
the supplied module docstring and DAG proof were followed. No statement was changed.

## Second reading by U2

1. Compared the sole delivered module against the repository with `diff -u`.
   PASS: the existing theorem signature and docstrings are byte for byte unchanged;
   only its proof and two plain, proof-only imports differ. There are no definitions,
   new declarations, or statement-change records in this delivery.
2. Compiled the delivered module with `lcompile.py`, with no errors or warnings.
   Compiled its scratch copy with `#print axioms exists_mem_maximalIdeal_smul_injective`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. PASS: no sorry remains,
   no holes were added, and there are no forbidden declarations or hollow definitions.
3. PASS: no statements were split off. Independently searched Mathlib with the launcher
   grep query `exists.*(regular|nonzerodivisor)|associatedPrimes.*maximalIdeal|maximalIdeal.*associatedPrimes`
   and searched both project roots for the same alternatives. No direct replacement
   theorem was found. Read the actual Mathlib regular-scalar characterization and
   finite prime-avoidance theorem. For the zero module, zero is injective and lies
   in the maximal ideal; the empty-family branch of prime avoidance handles this
   without a nonempty assumption. Over a field with a nonzero finite module, the
   hypothesis excludes its associated maximal ideal, as required.
4. PASS: the short proof uses Mathlib directly, with no project proof imports or new
   intermediate statements. Both added plain imports supply declarations used in the
   proof; the original public imports supply its statement's notions. All three old
   proof dependencies are still used, so `No longer needed: None` is complete.
   Read `dag/units/sk-thm-p1.json`: this auxiliary node is not a realization of the
   unit's statement or any step, and no unit route or realization is bypassed.
5. PASS: read the item's node and all three dependency nodes. Its proof is the
   contrapositive implementation of the recorded route: assuming every maximal-ideal
   scalar is nonregular places the ideal in the union, finiteness and prime avoidance
   give an associated prime containing it, and maximality forces equality. The
   existing `proof`, `proof_deps`, and document `proof_origin` accurately describe
   these same ingredients; no DAG change is necessary. There are no new nodes.

Second reading changed only this report. The Lean proof was retained unchanged.
The cited literature source is absent on this machine; the existing source attribution
was checked against the node and docstring, and the mathematical ingredients against
local pinned Mathlib source. No new literature claim or proof obligation was introduced.
