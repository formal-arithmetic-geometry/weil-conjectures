## What changed

Proved `IsRegularRing.quotient_span_singleton_of_isUnit_derivation` without changing
its signature or visibility. Added the proof-only import
`Mathlib.RingTheory.Localization.Ideal` for the quotient-localization instance.
The proof detects `D(f)` outside the inverse-image prime, extends the derivation,
proves the Leibniz contradiction by ideal-product induction, applies the existing
regular local hypersurface theorem, and transports it to each quotient localization.
Updated the existing node's proof to describe this argument; all four planned
proof dependencies and the unit route remain in use.

## Proved and sorry left

Closed one hole:
`IsRegularRing.quotient_span_singleton_of_isUnit_derivation`
(node `lem-weil-pbc-hypersurface-derivation-regular`).
No `sorry` remains in the assigned module; no holes were added or split off.
This is a proof from the existing stated dependency
`Derivation.exists_completion_and_unique_localization`
(node `lem-weil-pbc-derivation-extends`), whose existing `sorry` is unchanged.
The regular local hypersurface criterion used here is already proved in
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.
Single-file compilation passed without warnings.

## No longer needed

None. Both existing proof imports remain needed. The localization-of-quotient
and regular-ring-local-criterion nodes are realized using Mathlib directly;
the derivation-extension and regular-local-hypersurface nodes are applied as stated.
No nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The planned localized inverse relation is
unnecessary glue: a unit cannot lie in the quotient prime, so its original
representative lies outside the inverse-image prime and becomes a unit in the
localization immediately. The proof also needs no explicit branch for a unit
`f`: the local criterion quantifies over an empty set of quotient primes.
The source checkout search, LeanFinder query, and Loogle query found no shorter
regular-quotient theorem; the already proved local criterion supplies the last
local step. Stacks Tag 07PF was read at
https://stacks.math.columbia.edu/tag/07PF since its local literature file is absent
on this machine; its Leibniz and local quotient argument is exactly the one used.

## Second reading by Q1

1. Compared the only delivered module with the repository using `diff` and
   checked its existing theorem signature byte for byte: unchanged, including
   visibility. There are no new declarations, definitions or change records.
   Verdict: pass.
2. Independently compiled the module with `lcompile.py`: clean, 2.3 seconds.
   Scanned for `sorry`, axioms and forbidden implementation mechanisms: none.
   A scratch copy with `#print axioms` reports exactly `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx` for the delivered theorem.
   The latter is permitted here: the proof applies the existing, still open
   `Derivation.exists_completion_and_unique_localization`. Its localization
   clause uniquely determines the extended derivation, so obtaining that
   derivation does not choose arbitrary undetermined data. The local quotient
   criterion separately prints only the three standard axioms. Verdict: pass
   as a reduction to the existing dependency, not an axiom-free target proof.
3. No statements were split off, and no holes were added. Checked the small
   cases: unit `f` gives a zero quotient and no prime to consider; for `f = 0`,
   the unit hypothesis forces the zero ring; the argument makes no domain or
   characteristic assumption. Verdict: pass.
4. Independently read Stacks Tag 07PF at
   https://stacks.math.columbia.edu/tag/07PF (retrieved with curl after the web
   tool failed). Its regular-ring, unrestricted-element and unit-derivative
   hypotheses and conclusion agree exactly; its local Leibniz argument is
   implemented here with the localization details supplied.
   Read the proof from its conclusion downward and read the exact imported
   derivation-extension and local hypersurface statements. At a quotient
   prime, `f` maps to zero and `D(f)` is outside its inverse image; localization
   therefore makes the derivative a unit. Product-ideal induction uses the
   two Leibniz terms, each with a factor in the maximal ideal, establishing
   precisely the non-square hypothesis of the proved local quotient theorem.
   The quotient-localization instance and canonical algebra equivalence then
   give the requested prime localization. All proof imports are used; public
   imports provide the original signature's objects. Independent Loogle search
   `Derivation, IsLocalization`, LeanFinder search for the ideal-square/unit
   derivative argument, and searches of Mathlib derivations and both library
   roots found no shorter theorem. The `sk-thm-p1` unit's `realized` statement
   and all four step lists remain unchanged; this is below that unit's route.
   All four old proof dependencies remain used, so `No longer needed: None`
   is complete. Verdict: pass.
5. Compared the delivered node with the repository: only `proof` and
   `proof_origin` changed. Its three steps match the Lean argument and the
   union of their cited nodes is exactly the unchanged four `proof_deps`.
   The localization-of-quotient node records the exact Mathlib instance,
   prime-complement equality and equivalence used; the local criterion node
   records `isRegularRing_iff`; the other two nodes record the imported
   declarations applied. No new nodes require validation. Verdict: pass.

Changes made during second reading: appended this independent review only;
no Lean or DAG repairs were necessary. One existing hole closed, zero added,
zero split off, no imports or nodes pruned. The remaining transitive
`Derivation.exists_completion_and_unique_localization` hole is unchanged.
