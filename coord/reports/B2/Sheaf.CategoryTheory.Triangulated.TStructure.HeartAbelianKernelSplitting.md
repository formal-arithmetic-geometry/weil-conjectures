## What changed

Proved `CategoryTheory.Triangulated.TStructure.heart_abelian_and_idempotent_kernel_decomposition`
in `Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting`, with its
signature and visibility unchanged. The heart clause uses the existing proved upstream
`abelianHeart` with `hasHeartFullSubcategory`. The supplementary-kernel clause explicitly
constructs both maps, proves their inverse identities by kernel monicity and biproduct
extensionality, and verifies the specified conjugation of the idempotent.

Updated `prop-weil-heart-abelian`'s proof and proof origin to record this reuse and the actual
kernel calculation. Its proof dependencies remain: the existing upstream heart proof uses
all the recorded Mathlib leaves. No unit statement or step is bypassed; `sk-rem-rest` has
no realized statement or proof steps.

Searched using launcher leanfinder, loogle and grep, and local searches of Mathlib,
WeilConjectures and Sheaf. Search results supplied abstract Karoubi decompositions and the
idempotent-completeness criterion, but no theorem with the prescribed kernel inclusions
and projection. Read the upstream heart proof and Stacks `lemma-idempotent-splitting`.

Validation: remote single-file compilation succeeded after import pruning. A temporary
`#print axioms` command reported exactly `propext`, `Classical.choice`, `Quot.sound`;
the diagnostic command was removed from the delivered module. No new definitions or
statements, interface changes, consumer adaptations, or change records are needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Triangulated.TStructure.heart_abelian_and_idempotent_kernel_decomposition`
(node `prop-weil-heart-abelian`).

Holes added: 0. Split off: 0. Sorries left in the item or added elsewhere: none.
This is a complete proof, not a decomposition.

## No longer needed

Removed redundant direct proof imports:

- `Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory`
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`

Both remain available through the retained upstream heart module; its proof uses their
results. The recorded extension-closure, split-triangle and abelian-subcategory nodes are
Mathlib leaves used by that proof, so no DAG node or library module becomes unnecessary.
All public imports were kept because they provide the unchanged statement's vocabulary
and structures. No `tool_uses` approvals were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The DAG's original abelianity argument
already exists as a fully proved upstream theorem; it need not be reimplemented here.
The supplementary-kernel calculation follows the recorded plan and requires no added
hypothesis, including in the zero, identity, or zero-object cases.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
