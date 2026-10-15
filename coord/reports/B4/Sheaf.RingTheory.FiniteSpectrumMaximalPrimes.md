## What changed

Proved `Ideal.isMaximal_of_finite_primeSpectrum_of_finiteType` in
`lean/Sheaf/RingTheory/FiniteSpectrumMaximalPrimes.lean`. The proof imports
`Mathlib.RingTheory.QuasiFinite.Basic` and uses finite fibers, discrete prime spectrum,
and `Ring.krullDimLE_zero_iff`. The corresponding DAG node now records this Mathlib route
with no Sheaf proof dependencies.

## Proved and sorry left

Closed one existing hole:
`Ideal.isMaximal_of_finite_primeSpectrum_of_finiteType`.
Added zero holes and split off zero statements. No `sorry` remains in the delivered module.
The scratch-copy axiom check reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The entire old `proof_deps` list consisted of
`lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`; this planned DAG
dependency is no longer used explicitly by the Lean proof. It is a Mathlib leaf,
with no `lean.module` of its own, so no library module or existing import is removed.
The Jacobson intersection and finite-product argument are replaced by the quasi-finite API.
The two existing public imports remain necessary for the statement; the added
`Mathlib.RingTheory.QuasiFinite.Basic` import is proof-only. No modules are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was valid but unnecessarily long for Lean: Mathlib's quasi-finite and
Krull-dimension APIs prove the same statement directly. The theorem statement is unchanged.

## Second reading by B4

1. **Interfaces: pass.** Compared the complete delivered module with the repository
   version and checked the theorem signature byte for byte: the independent universes,
   field and ring hypotheses, algebra and finite-type instances, explicit finite-spectrum
   hypothesis, arbitrary ideal, primality hypothesis, and maximality conclusion are identical.
   There are no changed definitions, added declarations, or changes needing a change record.
2. **Proof and axioms: pass.** Compiled the module through `lcompile.py` without errors
   or warnings. Compiled a scratch copy ending in
   `#print axioms Ideal.isMaximal_of_finite_primeSpectrum_of_finiteType`; its only axioms
   are `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, forbidden declaration,
   hidden data construction, or nonstandard axiom occurs in the delivered module.
3. **Split statements: pass, none.** No statement was split off and no new node was added.
   Checked the zero ring case (no primes), a field, and a finite product of fields against
   the unchanged statement. The fiber-finiteness argument uses precisely the supplied
   `hfin`; no nontriviality hypothesis on `B` is introduced.
4. **Route and pruning: pass.** Read the Mathlib statements and proofs of
   `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`,
   `Algebra.QuasiFinite.discreteTopology_primeSpectrum`, and
   `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`, together with
   `Ring.krullDimLE_zero_iff`. Their hypotheses match each application. Searched the local
   ring-theory modules and Mathlib for finite-spectrum/maximal-prime alternatives; there is
   no exact existing theorem being restated. The existing valid proof needs no repair.
   Both public imports serve the theorem signature, and the sole private import supplies
   the proof. The report now lists the entire removed old `proof_deps` list accurately.
   Checked `dag/units/sk-prop-av-pqf-finite.json`: this node is an internal algebra lemma,
   not a recorded realization of the unit statement or its proper/quasi-finite theorem
   step. No unit realization or geometric route is changed. The unit's referenced
   blueprint source file is absent on this machine; its statement and step are recorded
   verbatim in that unit JSON.
5. **DAG: pass.** Compared the node JSONs: only `proof`, `proof_deps`, and `proof_origin`
   differ. The new proof records finite fibers, quasi-finiteness, discreteness, dimension
   zero, and maximality exactly as the Lean proof does. `proof_deps` is empty because
   every cited result is in Mathlib; `proof_origin` identifies the composed Mathlib route.
   The node's statement, Lean signature, source, unit, and blueprint association are unchanged.

Second reading changed only this report: made the one closed/zero added hole count explicit,
recorded the axiom check, corrected the claim that the removed Mathlib leaf had a library
module, and added this review. The Lean proof and node metadata required no changes.
