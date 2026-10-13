## What changed

Proved `AlgebraicGeometry.Spec.finite_setOf_isOpen_singleton_of_finiteType` without
changing its signature. Added the proof-only import
`Mathlib.RingTheory.Spectrum.Prime.Noetherian`. Finite type over a field yields a
Noetherian ring; Mathlib supplies the finite set of minimal spectrum points.
An open singleton is stable under generalization and therefore minimal. The final
argument is `Set.Finite.subset`. Updated the node's proof to match these steps.

The module compiles through `lcompile.py` without warnings. The proof uses no
project theorem containing `sorry` and introduces no intermediate statements.

## Proved and sorry left

Closed the only hole:
`AlgebraicGeometry.Spec.finite_setOf_isOpen_singleton_of_finiteType`
(node `lem-weil-pbc-finite-type-field-finite-isolated-points`).
One hole closed, zero holes added. No `sorry` remains in the delivered module.

## No longer needed

The proof no longer needs node
`lem-weil-pbc-spec-localization-away-basic-open`: there is no localization or
explicit basic-open selection in the Lean proof. Removed it from `proof_deps`.
No existing imports were removed and no project modules were pruned. The original
statement imports of Scheme and FiniteType are retained, and the new proof import
is used by `PrimeSpectrum.finite_setOfPred_isMin`.
The other two original dependency nodes remain used via their Mathlib declarations.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. Mathlib already packages both the finiteness of
minimal spectrum points and the generalization characterization of minimal
primes, making the original explicit basic-open step unnecessary. Searches using
LeanFinder, Loogle and grep were run through `msearch.py`; Loogle found
`PrimeSpectrum.finite_setOfPred_isMin`, and grep found
`PrimeSpectrum.stableUnderGeneralization_singleton`.
The unit `sk-thm-p1` was read: this node is below its realized statement and steps,
and the unit route is unchanged. No change record names this module.
The same proof covers the zero ring (empty spectrum), a field (one point),
polynomial algebras and finite products; no nontriviality hypothesis is added.

## Second reading by H4

1. **Visible declarations:** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and a proof-only import differ. Verdict: pass.
2. **Proof validity:** Compiled the module with `lcompile.py`; it compiles cleanly with no warnings, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and the proof introduces no new theorem holes. The finite-type Noetherian instance and Mathlib minimal-spectrum finiteness are used directly. Verdict: pass.
3. **Statements and dependencies:** No statements were split off or added. The existing theorem is proved at its original strength, and the node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof. The removed localization dependency is unnecessary because Mathlib's generalization lemma packages that argument. Verdict: pass.
4. **Shortest route and pruning:** Checked the imported declarations and Mathlib route. `PrimeSpectrum.finite_setOfPred_isMin` plus `stableUnderGeneralization_singleton` gives the direct subset proof; no shorter available project theorem was found. The unit `sk-thm-p1` route and realized statement remain intact. Verdict: pass.
5. **Edge cases and source agreement:** The unchanged statement agrees with the finite-type isolated-point claim, including the zero ring, a field, polynomial algebras, and finite products. No definition or target statement changed. Verdict: pass.

Changed during second reading: no Lean proof or DAG changes; added this review record only.
