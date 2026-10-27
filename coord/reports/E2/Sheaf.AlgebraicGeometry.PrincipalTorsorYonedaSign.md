## What changed

Reduce `AlgebraicGeometry.Etale.principal_torsor_yoneda_sign` to four independent results:
normalized adjunction comparisons, their naturality, coefficient Yoneda compatibility,
and the framed-extension calculation. The complete combining proof uses these results
and the existing signed torsor boundary theorem to derive the final negative localization
formula, including independence of the chosen cocycle representative.

The existing public comparison interfaces move to `PrincipalTorsorSignTypes`, re-exported
from the assigned module to avoid import cycles. Existing declaration names and statements
are retained. The actual localization sequence names its closed term; its equality with the
original construction was checked by reflexivity in the construction draft.
Change record: `coord/changes/principal-torsor-localization-cache.md`.

Repair of returned head `25917ab2861` (reviewer C-25917): retain the reviewed Lean
construction and decomposition, reconcile the packet with the current `sheaf-dag`
source, and compile all six modules against the current published server build.
Correct the change record to list all four comparison modules, including naturality.
The delivery tool recreates the commit on the fetched `origin/sheaf-dag` base.
The change record is part of the packet itself, so landing needs no change-record
override. All six Lean files and all six node files remain in the delivery.

## Proved and sorry left

All six delivered modules were recompiled through the required compiler with project
defaults after the packet repair (exit code 0). The combining module compiles in
8.6 seconds; the other files take 7.7–8.8 seconds.
The original hole in `AlgebraicGeometry.Etale.principal_torsor_yoneda_sign` is replaced
by a complete combining proof. Four independent
holes are added: `AlgebraicGeometry.Etale.principalTorsorNormalizedComparison`
(node `lem-pur-principal-torsor-normalized-comparison`) and
`AlgebraicGeometry.Etale.principalTorsorConnectingComparison`
(node `lem-pur-principal-torsor-connecting-comparison`). The third is
`AlgebraicGeometry.Etale.principalTorsorFramedComparison`
(node `lem-pur-principal-torsor-framed-comparison`). The fourth is
`AlgebraicGeometry.Etale.principalTorsorNormalizedNatural`
(node `lem-pur-principal-torsor-normalized-natural`). This is a decomposition, not a net
hole reduction: one closed and four added. The assigned module contains zero sorries.
No hole is inside a definition in the packet.

## No longer needed

The proof does not construct a new pushout or use relative-extension uniqueness: a morphism
from localization directly proves the specified extension-class identity.
`lem-weil-pbc-pushout-short-exact-sequence` and the proof use of
`lem-sp-relative-torsor-extension` are unnecessary. The latter remains a statement dependency.
The supplied degreewise split resolutions make `lem-weil-pbc-injective-resolution-ses`
unnecessary. Their obsolete top-level tool approvals are removed in order.

Remove the imports of `WeilConjectures.CategoryTheory.PushoutShortExactSequence`,
`WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`, and
`Mathlib.CategoryTheory.Abelian.Injective.Basic`. No module is withdrawn. Other consumers
may still need these nodes. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The direct short-complex morphism shortens the planned pushout construction and uniqueness
argument. The hypotheses already supply horseshoe data. The complete construction draft
was written and substantial focused pieces compiled, including the final torsor formula,
but the normalized construction and connecting glue remain separate proof obligations.
The signed equations agree with the node: beta is minus the differential cocycle and the
coefficient splice is minus the localization of the open coefficient boundary.

The previous landing failed while applying a reviewer fix named
`principal-torsor-localization-cache.md` at the fix directory root. The delivered
file is `coord/changes/principal-torsor-localization-cache.md`, retained in this
packet. The landing API expects a change-record fix basename ending in `.change.md`,
namely `principal-torsor-localization-cache.change.md`. The documentation corrections
are incorporated here, so they require no separate reviewer fix. No launcher or
landing tool changed.

The dispatcher replaced reference metadata on resumption: earlier start 1792670442.3862,
current start 1792730546.340239. The worker did not edit metadata and retained the original
deadline. No split is justified by elapsed time.

## New nodes

`lem-pur-principal-torsor-normalized-comparison` constructs the open and relative adjunctions
with their normalization. It contains no torsor or splice calculation.

`lem-pur-principal-torsor-connecting-comparison` proves coefficient Yoneda compatibility
for any normalized comparison using the supplied split resolution sequence. It contains
no existence assertion or framed-torsor calculation.

`def-pur-principal-torsor-sign-types` records the relocated existing public interfaces.
The relocation permits both independent statements without an import cycle.

`lem-pur-principal-torsor-framed-comparison` isolates the framed-extension pushout and its
negative relative cocycle. The assigned theorem combines it with the coefficient boundary
comparison and the existing signed torsor boundary theorem to prove the actual splice formula.

`lem-pur-principal-torsor-normalized-natural` proves coefficient and etale naturality of
any normalized comparison by uniqueness of signed cocycle representatives. Its remaining
hole is `AlgebraicGeometry.Etale.principalTorsorNormalizedNatural`.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
