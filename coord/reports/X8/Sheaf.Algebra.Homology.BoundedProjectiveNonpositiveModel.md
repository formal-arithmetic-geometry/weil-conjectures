## What changed

Withdraw the unused Sheaf.Algebra.Homology.BoundedProjectiveNonpositiveModel module
under brief step 8d. The existing upstream theorem of the same public name already
proves the stronger result with an explicit quasi-isomorphism. Reattach
lem-sc-bounded-projective-nonpositive-model to that declaration and record its actual
conclusion. Update the sole DAG citer's proof text to match its unchanged upstream
Lean proof, which converts the quasi-isomorphism to homology isomorphisms.

Change record: coord/changes/x8-bounded-projective-nonpositive-upstream.md.
No source-library file is changed. No new module or declaration is introduced.

Validation: the original assigned module compiled, as did separate copies of the
upstream producer and its sole caller. A scratch Lean example derives the exact old
conclusion from the upstream theorem. `#print axioms` for the upstream theorem lists
only propext, Classical.choice and Quot.sound. `downstream.py` and a full Lean import
scan confirm zero importers of the withdrawn Sheaf module. All verification files
are scratch files, excluded from the delivery.

## Proved and sorry left

Actual initial holes: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
This is duplicate retirement and DAG repair, not newly claimed proof progress.
CochainComplex.boundedProjective_nonpositiveModel and its private projective_cycles
helper were already proved in both copies. The upstream copies are preserved.
No statements are split off, and no declaration in the delivery uses sorry.

## No longer needed

Sheaf.Algebra.Homology.BoundedProjectiveNonpositiveModel is withdrawn: no Lean module
imports it, and the actual caller already uses the upstream theorem. Its duplicate
private projective_cycles helper and its local imports are thereby unnecessary:
Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex,
Mathlib.CategoryTheory.Abelian.Projective.Basic, and
Mathlib.Algebra.Homology.Embedding.TruncLEHomology. These Mathlib modules remain
needed by the unchanged canonical proof; no Mathlib module is withdrawn.

The node lem-sc-bounded-projective-nonpositive-model remains needed by
lem-sc-strict-perfect-closed-pushforward-stalk-resolution and now names the canonical
upstream declaration. No mathematical dependency node or unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned file contains no sorry and already compiles. The DAG still pointed at
its unused Sheaf copy and recorded the older, weaker conclusion. The current upstream
producer supplies a quasi-isomorphism, and the current upstream consumer already
uses it. The 2026-10-20 bulk retirement inventory conservatively retained this file
because the signatures differ; checking the actual consumer shows that retirement
is now safe. The zero complex, empty support interval and negative upper-bound cases
are covered by the unchanged explicit good-truncation construction and b.toNat bound.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
