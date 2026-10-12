## What changed

Proved `Algebra.quasiFiniteAtPrime_monogenic_integralClosure` with its signature unchanged.
Added the proof-only import `Mathlib.RingTheory.ZariskisMainTheorem` and removed the proof-only
import `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`.
Transported the isolated fibre point through `PrimeSpectrum.preimageHomeomorphFiber`, obtained
Mathlib's `Algebra.QuasiFiniteAt`, and applied its public finite-type Zariski Main Theorem.
Updated the existing node's proof, proof dependencies, and proof origin to this route.
No definitions, statements, visibility, public imports, or other modules changed.

## Proved and sorry left

Closed the only original hole: `Algebra.quasiFiniteAtPrime_monogenic_integralClosure`
(node `lem-weil-pbc-quasi-finite-monogenic-integral-closure`). No holes added or split off.
No `sorry` remains in the delivered module. This is a proof, not a decomposition.
The single-file compile passed cleanly through `lcompile.py`.

## No longer needed

Removed import: `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`.
Its theorem is not used by this proof. All three public imports remain needed by the statement.
The following former direct proof-dependency nodes are no longer needed by this theorem
(they may remain needed by other targets or modules):

- `lem-weil-pbc-finite-of-integral-generators`
- `lem-weil-pbc-finite-algebra-is-integral`
- `lem-weil-pbc-integral-transitive`
- `lem-weil-pbc-leading-coefficient-times-root-integral`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-reduced-strongly-transcendental-not-quasi-finite`
- `lem-weil-pbc-polynomial-ring-domain`
- `def-weil-pbc-strongly-transcendental`
- `def-weil-finitely-generated-module`
- `lem-weil-pbc-fibre-ring-primes-bijection`

The corresponding Sheaf module removed from this proof is
`Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`; no other Sheaf
proof module is imported. Mathlib implements the necessary algebraic theory internally,
so no claim is made that those facts disappear from Mathlib's theorem proof.

## Where the brief, the DAG or earlier work was wrong

The previous node correctly warned that the project and Mathlib quasi-finiteness notions
require a bridge. That bridge is only two rewrites through the existing fibre homeomorphism
and an application of the public `QuasiFiniteAt.of_isOpen_singleton_fiber`.
Once written explicitly, the public `ZariskisMainProperty.of_finiteType` proves the exact
conclusion, so the nine-step monogenic induction is unnecessary here. The item is not a
realized statement or proof step of `sk-thm-p1`; all of that unit's realized route is retained.
The source statement and the module's signature are unchanged, including degenerate rings:
if the quotient is the zero ring there is no prime q, and no nontriviality assumption was added.

Searches: launcher `leanfinder` and `loogle` both found the public Zariski Main declarations;
`rg` over both library roots and pinned Mathlib found no alternate project proof. Read the
Mathlib definitions and theorem signatures directly. No new lemma or node is required.

Rechecked the earlier sandbox attempt: its proof compiles cleanly. Removed the stale
fibre-bijection dependency from the first proof step so that the union of step dependencies
agrees with `proof_deps`. Removed the earlier second-reading section for independent review.

## Second reading by D2

1. **Visible declarations and statements.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof-only import and proof body changed. The DAG node's statement is unchanged.

2. **Proof validity.** Compiled the delivered module with `lcompile.py`; compilation succeeds with no errors and the module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses the Mathlib fibre homeomorphism to transport the isolated singleton, then `QuasiFiniteAt.of_isOpen_singleton_fiber` and `ZariskisMainProperty.of_finiteType`. The resulting witness is definitionally the requested integral-closure element and localization bijection. The target's finite-type instance is the polynomial-quotient instance, including degenerate cases.

3. **Statements and dependencies.** No new theorem or split-off statement was added. The existing node's statement remains exactly as written and is proved at its full strength. The updated `proof` and `proof_deps` list only declarations actually used by the shorter proof; removed old induction dependencies are recorded in `## No longer needed`.

4. **Pruning and route.** The proof takes the shorter public Zariski Main route and removes the unused project theorem import `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`. The unit's realized route is unchanged; this is a below-unit proof shortcut using the same target statement.

5. **Node agreement and review verdict.** The node proof steps, dependencies, and origin match the Lean proof, and the node remains attached to the same unit and chapter. No new node or change record is needed. Verdict: approved after the checks above.

No additional changes were needed in this second reading.
