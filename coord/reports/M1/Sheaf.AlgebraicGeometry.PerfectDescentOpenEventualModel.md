## What changed

Completed `AlgebraicGeometry.perfect_descent_open_eventual_model` without changing its
signature. The proof applies the given descent predicate to the inverse-image open,
pulls its model to each later index, and transports the comparison through explicit
cartesian open identifications. Added three proved private helpers:
`openBaseChangeIso`, `openBaseChangeInclusion`, and `openBaseChange_transport`.
Added proof-only imports `Sheaf.AlgebraicGeometry.DerivedPullbackPerfect`,
`Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData`.
Updated the existing node's proof route and dependencies. No public interface changed.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.perfect_descent_open_eventual_model`
(node `lem-pc-perfect-descent-open-eventual-model`). No holes added, none split off,
and no sorry remains in the delivered module. The scratch `#print axioms` probe reports only `propext`, `Classical.choice`,
and `Quot.sound`, so the proof also has no imported sorry dependency.

## No longer needed

The planned dependency `lem-pc-derived-pullback-open-restriction-universes` and its
module `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses` are unnecessary
for this proof. All scheme derived categories here use the same universe w; the
existing `singleComplexOpenPullbackIso` suffices after explicit composition.
This dependency was not imported in the original item, so no import was removed.
The other original imports remain necessary for the unchanged statement.
No claim is made that the pruned module is absent from other target branches.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's universe-general restriction comparison is more
than this item needs; its role is replaced by the already constructed canonical open
pullback comparison. The unit record has no realized nodes, and no unit statement or
step is bypassed. Empty opens give the same cartesian identifications; k = j and
non-antisymmetric preorders work because homOfLE and cocone identities do not require
strictness or antisymmetry. No colimit hypothesis is used or added.

The saved attempt used file-level elaboration options, which preflight classified as
an interface change. Scoped both transparency options to the four declarations that
use them, keeping the public interface and theorem signature unchanged. The delivery
wrapper now filters diagnostics originating in its own appended probe.


## Second reading by M1

1. Compared the entire delivered module with the repository version. The existing
   theorem signature and docstring are byte-for-byte unchanged. Only private helpers,
   declaration-scoped elaboration options, proof-only imports, and the proof are added.
   No definition or existing public visibility changed; no change record is required.
2. Compiled the module successfully with lcompile.py. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.perfect_descent_open_eventual_model`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Inspected all
   three private helpers: cartesian identifications and inclusion maps are constructed,
   and the transport proof composes actual isomorphisms. No forbidden declaration,
   hollow definition, or remaining sorry occurs. Verdict: a complete proof.
3. No split-off theorem or new public statement exists. The descent witness is obtained
   inside a proof, not used to define arbitrary data. Empty opens, k = j, and preorders
   with mutually comparable distinct elements introduce no additional assumption.
   Verdict: no new hole or statement to validate.
4. Read the descent predicate, perfect pullback theorem, and canonical open comparison;
   searched the local descent and pullback modules for an existing shorter result.
   The proof uses the predicate directly, then composition and cartesian restriction;
   no existing theorem in that chain replaces this argument. The two new Sheaf imports
   are proof-only and used. The old proof dependency removed is precisely
   `lem-pc-derived-pullback-open-restriction-universes`, as listed above. The unit's
   `realized` record is empty and unchanged; no realized statement or step is bypassed.
   Verdict: route and pruning agree. Removed the redundant direct proof import of
   `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`; a scratch copy
   compiles without it, using the imports already available.
5. Compared the original and updated node records: parsed statements and Lean signature
   agree, and the only semantic edits are proof, proof_deps, and proof_origin. Each
   dependency occurs in the proof; their union matches proof_deps. The three steps
   accurately describe descent, stage enlargement, and explicit open transport.
   No new node is required for proved private helpers. Verdict: DAG agrees with Lean.

Second reading changed only the redundant proof import and this report (including
recording the clean axiom probe). The mathematical proof is retained unchanged.
