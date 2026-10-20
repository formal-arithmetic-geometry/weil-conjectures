## What changed

Retired `Sheaf.RingTheory.TensorModelPushoutBaseChange` in favor of its unchanged
upstream twin, as assigned by `coord/retire-items.tsv` (depth zero, consumers zero).
The withdrawal is recorded in `deleted.txt`. Repointed the sole attached node,
`lem-pc-tensor-model-pushout-base-change`, to the upstream declaration and copied
its exact signature into the Lean record. The node's statement and proof route stay
unchanged. Change record:
`coord/changes/retire-tensor-model-pushout-base-change-T4.md`.

## Proved and sorry left

Original holes: zero. Holes closed: zero. Holes added: zero. Holes left: zero.
No split-off statements or new nodes.

`AlgebraicGeometry.tensor_model_pushout_base_change` already has a complete proof
in both copies. The upstream statement additionally fixes the induced P-algebra
structure. In the sandbox-only `scratch/Verification.lean`, proved the old exact
signature from the upstream theorem by unpacking the initial algebra witness and
reintroducing the induced final algebra witness. lcompile.py compiled this check
in 1.5 seconds. Both declarations' axiom checks list only propext, Classical.choice,
and Quot.sound. No axiom or proof hole was introduced.

## No longer needed

Module `Sheaf.RingTheory.TensorModelPushoutBaseChange` and its duplicate theorem
are withdrawn. It has no consumers, so no consumer imports require rewriting.
Its public import of Mathlib.RingTheory.IsTensorProduct disappears with the copy;
the upstream twin retains the required import. The node remains needed and now
refers to the upstream twin. No other module or node is pruned.

Searches: msearch.py LeanFinder found tensor pushouts and base-change cancellation;
Loogle found Algebra.IsPushout.comp_iff. Source searches found the exact upstream
twin and its sole upstream call site. The upstream proof already implements the
same cancellation-and-pasting argument; no new proof infrastructure is needed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a repeatedly split obligation, but the current
queue assigns a retirement with zero holes and zero consumers. The existing DAG
Lean attachment still named the unused Sheaf copy. The upstream theorem has a
stronger interface (explicit input P-algebra and prescribed output P-algebra),
which implies the recorded mathematical statement without extra hypotheses, as
verified by the compiled compatibility proof. No unit route is bypassed.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
