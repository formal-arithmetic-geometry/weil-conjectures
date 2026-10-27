## What changed

Completed `WeilConjectures.SemilinearSections.sequenceSiteCompletionProjection` in
`Sheaf.Paper.SequenceSiteCompletionProjection`.

The proof constructs the constant/limit adjunction for set sheaves, the cone's
structural ring map, and the module direct image as the limit of actual scalar
restrictions. It transports the existing ordinary extension system and adjunction
from `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction` through the
strict-system/sequence-site equivalence. Its unit and transition normalizations
are verified on sections. A resolving class of flat-term K-flat complexes supplies
one left-derived functor before evaluation. Comparison on this common resolution
class gives every level evaluation isomorphism and its representative square.

The equivalent section interfaces in `SequenceModuleRestriction.moduleDirect_section`,
`SequenceOrdinaryPullback.ordinary_unit`, and `ordinary_transition` are normalized
to avoid expanding entire module actions while matching transported sections.
The first two use heterogeneous equality with the existing object identifications;
the third composes actual module maps before evaluation. These retain the original
coordinate and tensor insertion conditions. Explicit category arguments resolve
otherwise expensive elaboration metavariables. The theorem statement, coefficient
universes, and hypotheses are unchanged. Instance selection during elaboration avoids
the generic multicospan route in favor of the existing specialized forgetful
composition instances and size-bounded limit preservation. Private
comparison definitions are hidden after their coordinate formulas are proved, and
the module-linearity calculation combines those formulas directly. Scalar-model
preservation under an equivalence, resolving-class derivation, and
the final record assembly use proved generic private helpers. Explicit cached tower-limit
instances avoid repeating size-instance searches. Declaration linters are disabled in this module to avoid
repeated traversal of transported coordinate proof terms.
Lean kernel checking and delivery preflight remain enabled.

Change record: `coord/changes/sequenceCompletionProjectionCompatibility.md`.
No source-library declaration or target declaration was changed. No downstream
adaptation is required: the existing consumers do not use the changed fields.
The node's proof and dependencies now describe the implemented construction.
The vertical-slice sheaf criterion reuses the existing sequence-site theorem, and
the ordinary evaluation maps are identity maps on sections by reflexivity.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SemilinearSections.sequenceSiteCompletionProjection`
(node `lem-pur-sequence-site-completion-projection`).

Holes closed: 1. Holes added: 0. Holes remaining in the item: 0.
No statements were split off. All new private helpers have complete proofs.
Existing imported statements are used as the stage-3 dependencies; their own holes
are not moved or replaced by this packet.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.RingedTopoiDerivedPullback`;
- `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `Mathlib.CategoryTheory.Preadditive.Injective.Preserves`.

These modules remain transitively imported by the reused dependency library;
this packet does not withdraw any module or claim that they are globally unused.

The proof no longer calls the planned general ringed-topos derived-pullback
construction (`lem-weil-pbc-ringed-topoi-derived-pullback`), nor its
`lem-pur-derived-change-of-rings` comparison. Instead it derives the explicit
ordinary extension using the resolving-class construction, and compares the
result on a common class of resolutions. Removed the obsolete general-pullback
entry from `tool_uses`; retained `lem-pc-kflat-resolution`, in the original order
(coord/brief-stage3.md §6 permits deleting obsolete approvals).

The other removed direct proof-dependency entries are
`lem-weil-pbc-equivalence-injective-resolutions` (the completion equivalence is
definitionally the identity, so identity instances suffice),
`def-pur-system-level-left-extension-basic`, `def-weil-pbc-sites-and-cohomology`,
`def-weil-pbc-ringed-topos-morphism`,
`lem-pur-sheaf-ring-coefficient-ordinary-adjunction`, and
`def-pur-sheaf-tensor-product`. The implemented proof uses the existing
sequence-system equivalence, the item's independent-universe ringed-topos
interface, and the already constructed scalar models rather than separately
invoking those planned steps. Definitions still needed by statements or by
imported dependencies remain in the library. The blueprint unit has no realized
proof-step nodes to bypass, and its six-operation route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original nested section expressions were mathematically correct but expensive
to elaborate: Lean repeatedly unfolded scalar actions and chosen limits when
matching their carriers. The equivalent interfaces recorded above make those
identifications explicit and permit checking the actual section maps.

The DAG's general derived-pullback route was unnecessary given the existing
explicit sequence extension and the resolving-class normalization results.
No mathematical statement was disputed or weakened. No new nodes were introduced.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
