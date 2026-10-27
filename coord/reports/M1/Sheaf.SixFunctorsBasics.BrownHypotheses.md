## What changed

Reused the coefficient-independent structural theorem in two existing complete proofs.

In the assigned item, `CategoryTheory.brownHypothesesFor_iff` now takes the local
smallness, triangulation, repleteness and idempotent-completeness witnesses directly
from `brownHypotheses_structural`. Its reverse direction supplies compactness from
its existing hypothesis and proves generation with `localizingClosure_generatingFamily`.
Removed the now-unused private helpers `localizingClosure_isLocalizing` and
`brownHypothesesFor_of_compact`; no public declaration was removed or changed.
The inherited triangulation is registered explicitly for the generic localizing
closure before applying the generation theorem.

In the unclaimed module `Sheaf.Paper.BrownExceptionalAdjoint`, replaced the direct
call to the disputed arbitrary-field `brownHypotheses` theorem with the proved
`brownHypotheses_structural Λ Y`. The theorem already assumes source compact
generators, and its original proof extracts only structural clauses at the target.
The existing theorem statement, functors, canonical comparison maps, adjunctions,
shift compatibility and coherence proof are unchanged. Its proof import now names
`Sheaf.SixFunctorsBasics.BrownHypothesesStructural`.

Updated the formal criterion and exceptional-adjoint DAG proofs to match.
No new node, coefficient notion, definition, axiom, proof hole or target change.
Change record: `coord/changes/M1-brown-structural-witness-reuse.md`.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The sole remaining sorry is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`. Its signature, disputed warning and original proof hole
remain unchanged. The modified formal criterion and exceptional-adjoint theorem
have complete proofs. This delivery removes an unnecessary direct use of the
disputed theorem; it does not claim to prove that theorem or close its hole.

The adapted exceptional-adjoint module compiled successfully in 17.8 seconds.
The first item compile identified explicit instance registrations needed by the generic
localizing-closure generation lemma. The canonical structural triangulation and
chosen coproduct structure are now registered for the generic closure; its actual
representative family has an explicitly typed coproduct witness. The corrected
assembly scratch probe compiles cleanly in 19.2 seconds. Earlier full runs reached
the 60-second limit while the failed instance search remained. The final full item compiles cleanly in 57.3 seconds, with no profiling commands
and no warnings. No file was split and no limit was raised.

A declaration-level source comparison confirms every retained signature unchanged,
no new declaration, and no non-theorem body change. The two removed declarations
are private proved helpers in the Sheaf item; neither has an external user.
All Lean lines satisfy the 100-character limit. JSON changes are confined to
`proof`, `proof_deps` and `proof_origin`.

## No longer needed

Removed the direct proof import `Sheaf.SixFunctorsBasics.BrownHypotheses` from
`Sheaf.Paper.BrownExceptionalAdjoint`, replacing it with the structural module.
The parent node `det-sf-existence-brown` no longer needs
`sk-lem-brown-hypotheses` as a proof dependency: the target structures come from
`h1-brown-hypotheses-structural`, and source compact generation is already assumed.
Its statement citation explaining that source assumption remains unchanged.

Removed private helper proofs `localizingClosure_isLocalizing` and
`brownHypothesesFor_of_compact` from the item, since the proved structural theorem
and direct criterion assembly provide their only needed conclusions.

No whole module is withdrawn or pruned from the targets' import closure.
BrownExceptionalAdjoint's unchanged public import LocalizingExceptionalAdjoint
still reaches BrownHypotheses. The other two callers actually use compactness,
so their calls and DAG dependencies remain. No quarantined parent is deleted or
used as evidence of withdrawal. All item proof dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `CategoryTheory.brownHypotheses` still claims compactness over
an arbitrary positive-characteristic field, whereas its supplied compactness
input requires the algebraic closure of a finite field. Finite type over an
arbitrary field does not supply a finite-field datum or finite absolute
cohomological dimension. The existing infinite-transcendence-degree Kummer-symbol
diagnostic remains a natural-language reason for the dispute, not a formal Lean
counterexample. No false arbitrary-field compactness statement is split off.

The consumer's DAG and proof had unnecessarily invoked that disputed compactness
bundle to obtain purely structural properties of Y. This delivery implements
the existing structural step directly. The unit's Brown-representability route,
source compact-generation assumption, exactness and coherence steps all remain.
Edge cases include empty schemes, zero coefficients and empty compactification
families: the replacement structural theorem is valid without admissibility or
geometric restrictions and returns the same canonical inherited shift.

Searches used launcher LeanFinder (eight t-structure/HasExt infrastructure results),
Loogle for IsCompactObject (zero results), launcher grep for the existing structural
and compactness-criterion names (zero results), and direct rg over Mathlib, Sheaf
and WeilConjectures. Direct source inspection found the proved structural theorem
and verified the actual field restriction in the finite-field compactness input.
No existing valid arbitrary-field compactness declaration was found.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
