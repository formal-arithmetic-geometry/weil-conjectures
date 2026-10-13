## What changed

Kept `AlgebraicGeometry.perfect_hom_open_stage_presentation` and its signature unchanged.
Constructed B = t inverse-image W, Z = B.toScheme, k = B.ι followed by t and
s' = B.ι followed by s directly. Proved the image equation and all morphism-property
instances using Mathlib. Fixed P' = LP[-n] and Q' = LQ explicitly.

`PerfectHomOpenStageData` now PROVES the localized category construction and perfection
of these specified endpoints. Its private helpers reuse the proved localization and
exact-restriction arguments from `PerfectRestrictionClassesSmall`, and the shift-model
argument from `PerfectTwoOutOfThree`. All proof-only imports are plain imports.
`PerfectHomOpenStageMaps` now states only the compatible Hom comparisons for those
specified endpoints, with a complete source-based natural-language proof.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.perfect_hom_open_stage_presentation` by
explicit geometry/perfect-object construction and composition. Added and proved
`AlgebraicGeometry.Scheme.perfect_hom_open_stage_data`
(node `lem-pc-perfect-hom-open-stage-data`). One new named hole remains:
`AlgebraicGeometry.perfect_hom_open_stage_maps`
(node `lem-pc-perfect-hom-open-stage-maps`). No other delivered declaration has sorry.

This is a decomposition: one original hole closed, one lower hole added, net zero.
The geometry, category-instance construction, and perfectness are now proved; the
strictly smaller compatible Hom-comparison part remains open. Relative to the first
worker's sandbox, the data hole is closed and the invalid arbitrary-endpoints maps
statement is replaced.

## No longer needed

No existing public import or module was pruned. The target's old direct proof dependencies
`def-pc-perfect-complex`, `lem-pc-perfect-hom-push-pull-cocone`,
`lem-pc-perfect-hom-transport`, `lem-pc-restrict-derived-direct-image-open`,
`lem-pc-ringed-spaces-derived-adjoint`, and
`lem-pc-ringed-spaces-derived-pullback-composition` are replaced at this node by the data
and maps nodes; the lower proof plans still record the dependencies they actually need.
`def-pc-derived-mayer-vietoris-canonical-data` stays a direct dependency.
Removed the unnecessary PushPullCocone public import from the new Data module, replacing
it with PerfectComplex, which its statement needs.

## Where the brief, the DAG or earlier work was wrong

The first worker's maps statement quantified over arbitrary perfect P', Q', with no
relation to P,Q. That is false: take the total open of Spec of a nonzero field, a
singleton identity ring diagram, n=0 and P=Q=the unit, with its identity representing
system. Hom(P,Q) has distinct zero and identity maps; choosing P'=Q'=0 makes the
right Hom set a singleton. The initial data theorem did not pin the endpoints either.
The maps docstring lacked its proof, new nodes lacked searches, and the parent node
was not updated. Those defects and the letI linter warnings were repaired.

## Second reading by W2

1. Compared every existing declaration with the repository: the original target
   signature and docstring are byte-for-byte unchanged. Only proof imports and body
   changed. New declarations are confined to new modules. Verdict: pass after repair.
2. Compiled all delivered modules with lcompile.py. Only the named maps theorem
   remains sorry; there are no hollow definitions or forbidden declarations. Checked
   the declarations' axiom closures with scratch #print axioms and the delivery probe.
   Verdict: pass subject to the explicitly reported maps hole and imported open results.
3. Rejected the arbitrary-endpoints maps statement by the small counterexample above.
   Its repaired statement fixes LP[-n], LQ and is exactly the Hom-comparison step.
   The data statement is proved. Attempted LeanSearch (service unavailable), and performed leanfinder, loogle and grep searches with
   new queries, and searched the repository for restriction/perfectness/shift results.
   Reused existing pullback perfection and generic restriction/adjunction APIs.
   Tested the empty open, zero objects, total open and n=0 in the source argument.
   Verdict: pass after repair.
4. The top proof now constructs its objects and geometry first, then uses proved
   perfection, and only leaves the compatible comparisons open. Imports serve either
   statements or the actual proof. Read sk-thm-picard-semicon.json: its realized fields
   are empty and this below-unit reduction changes no unit statement or step.
   Verdict: pass.
5. Updated the parent proof, proof_deps, and proof_origin. Rewrote new-node statements,
   proof steps, verbatim Lean signatures and search records to match the repaired Lean.
   The two new nodes have the same chapter/unit as the parent. Verdict: pass.

Second reading changed the false maps interface, proved the data lemma, constructed
all existential geometry and endpoints explicitly, repaired warnings and import
visibility, and completed node metadata and this report. No change record is needed:
no existing statement or definition changed.

## New nodes

`lem-pc-perfect-hom-open-stage-data`: proved construction of local derived categories
and perfection of specified exact restrictions and shifts, in
`Sheaf.AlgebraicGeometry.PerfectHomOpenStageData`.

`lem-pc-perfect-hom-open-stage-maps`: remaining compatible stage/apex Hom comparisons
for the specific restricted endpoints, in `Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps`.
