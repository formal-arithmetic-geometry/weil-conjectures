## What changed

Proved `Algebra.isGeometricallyRegular_fiber_of_localizations_maximal` in the sandbox. The proof first verifies regularity of each finite purely inseparable base change of the fibre. It uses the tensor-product cancellation equivalence, chooses a maximal ideal over each prime of the extended fibre, identifies the corresponding localization with the tensor product of the localized target fibre, and transports regularity back through localization at a prime. Added only the Mathlib imports needed for tensor-product finiteness, localization base change and localization of localizations. Updated the existing node’s proof, proof dependencies and proof origin to match the compiled proof.

## Proved and sorry left

The module theorem `Algebra.isGeometricallyRegular_fiber_of_localizations_maximal` is proved. Closed the only original hole (node `lem-weil-pbc-geometrically-regular-fiber-of-maximal`). No `sorry` remains; zero holes were added. The private helper `Algebra.regular_tensor_of_maximal` is also proved. This is a proof, not a decomposition. Local compilation was clean; the delivery dry run checks the axiom probe.

## No longer needed

The prior proof-only import `Sheaf.RingTheory.LocalizationOfRegularRing` is no longer needed; the proof uses Mathlib localization and tensor-product equivalences directly. The proof does not need node `lem-weil-pbc-localization-of-regular-ring` or its module `Sheaf.RingTheory.LocalizationOfRegularRing`. It also replaces the planned finite-type Noetherianity dependency `lem-weil-pbc-finite-type-algebra-noetherian` by the finite-algebra result `lem-weil-pbc-finite-algebra-noetherian`. The unit statement and steps are preserved; this item is not itself a unit realization.

## Where the brief, the DAG or earlier work was wrong

The planned intermediate localization-of-regular-ring theorem was stronger than necessary. Mathlib's `IsRegularRing.of_ringEquiv`, `isRegularRing_iff`, localization-at-prime equivalences, and tensor-product localization equivalences suffice directly.

## Second reading by F3

1. **Statements unchanged.** Compared the delivered module with the repository version; the public theorem signature is byte for byte unchanged. The node updates only proof-owned fields (proof, proof dependencies, and proof origin). Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it is clean, contains no `sorry`, forbidden declarations, or hollow definitions. The proof uses the stated tensor cancellation, localization, and regular-local criterion steps. Verdict: pass.

3. **Split statements.** No statements were split off and no new nodes were added. The private helper is a genuine intermediate reduction, fully proved. Verdict: pass.

4. **Shortest route and pruning.** Checked the imports and proof dependencies against the proof: the former localization-of-regular-ring dependency is unused, while tensor-product finiteness and localization equivalences are used directly. The finite-algebra Noetherianity dependency replaces the unnecessary finite-type route. Verdict: pass.

5. **DAG and unit route.** The node proof text, dependencies, and origin agree with the Lean proof, and the unit statement and route remain intact. Verdict: pass.

Changed after second reading: no Lean declarations or statements; this section records the verification above.
