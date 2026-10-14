## What changed

Verified the already repaired module Sheaf.RingTheory.ZariskisMainAway and shortened
Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime's openness transport to an explicit
application of Homeomorph.isOpen_image.mp and Set.image_singleton. The original and revised
proofs compile. The signature, visibility, imports, definitions and proof route are unchanged.
Mathlib's QuasiFiniteAt.of_isOpen_singleton_fiber supplies the finite-type criterion.
The three existing callers already use this conversion before applying Mathlib's
ZariskisMainProperty.of_finiteType themselves.

## Proved and sorry left

Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime is fully proved. It was already proved
in the assigned repository version: zero holes closed, zero holes added, zero holes left.
This is verification and proof simplification of the still-listed repair, not new proof progress.
There is no decomposition and no new theorem. The dry run checks the allowed axioms.

## No longer needed

None newly pruned. Each existing import is needed: Mathlib.RingTheory.QuasiFinite.Basic
provides the public result type; Sheaf.RingTheory.QuasiFiniteAtPrime provides the public
hypothesis; Mathlib.RingTheory.ZariskisMainTheorem provides the proof criterion.
No blueprint unit step is bypassed. The existing node
lem-weil-pbc-integral-closure-zariski-main-away already points to Mathlib's theorem and
records the conversion helper in its first proof step; its route remains accurate.

## Where the brief, the DAG or earlier work was wrong

The dispatched brief says this module still contains sorry, but it contains none.
The repair remains in coord/repairs.txt although the K2 interface repair was landed as
recorded in coord/changes/zariskisMainProperty-wrapper-removal.md. In particular this
module no longer duplicates the Zariski-main localization conclusion. No statement or
definition correction is needed. Loogle, Lean Finder and the Mathlib source search
confirm the exact finite-type singleton-fibre criterion already used by the proof.

## Second reading by E3

1. **Visible declarations and accidental changes.** Compared the delivered module with the repository version. The theorem signature, visibility, imports, definitions, and documentation are byte-for-byte unchanged; only the proof term changed. Verdict: pass.
2. **Proof and axioms.** Compiled the sandbox module with `lcompile.py`; it compiles without errors or warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The revised theorem uses only the existing Mathlib criterion and the fibre homeomorphism; its allowed axioms are unchanged. Verdict: pass.
3. **Statements and split-offs.** No declarations were split off and no new nodes or statements were added. The existing conversion theorem is unchanged and is strictly weaker than the Zariski-main conclusion it enables. Verdict: pass.
4. **Route and pruning.** The proof keeps the unit's conversion step and then leaves the Zariski-main conclusion to the existing Mathlib theorem in its callers. All imports remain needed; no old proof dependency or module can be pruned from this delivery. Verdict: pass.
5. **DAG agreement.** The existing node's statement and proof dependencies still match the theorem and its callers. The node's recorded conversion step agrees with the explicit `isOpen_image.mp` and `Set.image_singleton` proof. Verdict: pass.

Changed after reading: replaced the rewrite-based openness transport with the direct `Homeomorph.isOpen_image.mp` application and an explicit simplification of the singleton image. No interface, statement, node, or import changed.
