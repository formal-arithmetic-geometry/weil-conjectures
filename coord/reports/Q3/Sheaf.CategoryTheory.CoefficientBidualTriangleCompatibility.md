## What changed

Completed `CategoryTheory.CoefficientBidual.slice_compatibility` with its original
signature. The main module now proves the restriction evaluation square by closed
adjunction transposition and coefficient transport; builds the double-dual natural
isomorphism from the single-dual comparison and its right opposite; proves its shift
compatibility with the supplied normalized bidual shifts; and derives the triangle's
connecting-map equation from naturality. No biduality or evaluation map is cancelled.

Added `Sheaf.CategoryTheory.RingedSiteSignedDualRestriction`. Its theorem
`CategoryTheory.ringedSiteSignedDual_restriction` is proved from the existing normalized
comparison, evaluation-coherence and Koszul-coherence declarations, and the narrower
source-shift theorem below. Its proved `closedDualRestrictionIso` definition packages
single-dual restriction including coefficient transport. The proof identifies the
normalized comparison symmetries with the supplied duality-model symmetries on K-flat
representatives, so it does not substitute arbitrary comparison data.

Added `Sheaf.Algebra.Homology.RingedSliceHomSourceShift`, containing the separate ordinary
Hom source-reindexing restriction calculation and its derived localization square.
This is a genuine part of the source construction: its conclusion concerns a single
Hom in arbitrary source and target objects, with no bidual, evaluation transformation,
triangle, or invertibility assertion. Private proved helpers identify the inverse
augmentation-normalized Hom model with the ordinary comparison and establish the
source-shift equation on that model. The signed chain-map restriction square is also
fully proved as `restriction_sourceShift_chain`, using equality on local Hom-family
components and the two projection formulas. The localization shift identity and the
formula for the derived comparison on normalized models are also proved as private
helpers `localization_shift` and `hom_restriction_model`. The left side of the
conjugated model equation is proved as `sourceShift_model_restriction_left`. The
remaining source hole is the right-side assembly, cancellation, and transport to
arbitrary representatives. Naturality of the ordinary
Hom comparison in its source is proved as `ordinaryComparison_source`, reusing the
private ordinary-to-derived natural transformation via a private `import all` of
the existing normalized shift module.

All existing public signatures, definitions and public imports are preserved. Added
imports in the main module are private proof imports. No adopted source-library module
is edited. No forced adaptation is needed. The preflight command-index change is
documented in `coord/changes/q3-coefficient-bidual-slice-proof.md`; it records the
private proof context, local instance registration, unchanged existing signatures,
and the two new source interfaces.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.CoefficientBidual.slice_compatibility`
(node `lem-coef-rational-bidual-triangle-compatibility`). The item module has zero
remaining holes. All its original other theorem proofs remain complete.

Added one hole:
`CategoryTheory.ringedSlice_hom_sourceShift`
(node `lem-coef-slice-hom-source-shift`). Its proof is a whole named public theorem
body, with source and complete natural-language proof in its docstring and node.
No definition contains a hole. The new single-dual wrapper theorem is fully proved
from this and the existing declarations.

Thus this is a decomposition: one upper hole closed, one strictly narrower source hole
added, net zero among declarations changed by this packet. It is not an
unconditional proof of the biduality theorem.
The imported normalized comparison and signed exactness declarations already have
holes; these are existing declarations, not new holed declarations added here.
The sorry ledger determines the effect on the full targets import closure.

The three modules have compiled together through lcompile. All single-file runs are
below the 60-second limit (the final combined run: 28.9, 37.4 and 34.8 seconds;
with the additional ordinary-comparison and model-left helpers the source module
compiled in 41.9 seconds; the item with local shift-instance registration
compiled in 34.7 seconds). The new formula was checked at zero and negative shifts,
in characteristic two, on zero complexes and on an arbitrary slice. The construction
does not assume reflexivity, boundedness or perfection. Its coefficient transport uses
an arbitrary coefficient-object isomorphism and proves the two inverse transports
cancel functorially.

## No longer needed

No import of the original item module is removed. The new wrapper's unused preliminary
Mathlib opposite-functor import was removed before delivery. It imports only the
normalization, evaluation, Koszul and single-Hom source-shift results used in its proof.

The main node's direct proof edges to `def-pur-hom-complex`,
`def-pur-kinjective-complex`, `def-pur-localized-ringed-site`,
`lem-pur-rhom-well-defined` and `lem-sf-double-hom-cone-comparison` are unnecessary for
the new categorical slice assembly. Ordinary Hom and K-injective details are recorded
under the new source node, and cone comparisons remain relevant to the existing
ambient evaluation source theorem. These are redundant direct edges, not withdrawn
modules. No module or node is claimed globally pruned. The unit's route and all
existing declaration attachments are preserved; no file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The former slice plan used the existential restriction theorem for duality maps as
though it fixed the particular derived restriction functor and included normalized
source-shift coherence. It does not provide that coherence. The proof now uses the
actual fixed restriction comparison, its representative normalization, and the separate
signed source-reindexing square. Naturality alone cannot imply that an arbitrary
natural isomorphism commutes with prescribed shift structures.

There is no disputed statement and no weakening of any existing conclusion. The
connecting-map equality actually needs only naturality and shift compatibility; it
holds for every triangle. The distinguished-triangle hypothesis is retained verbatim.

## New nodes

`lem-coef-slice-hom-source-shift` states restriction compatibility of the uniquely
projection-normalized source shift of a single derived Hom. Its source is Stacks
08JB, 08FI and the Hom-complex construction in 0A8X. Its representative calculation
uses the same reindexing and sign on both sites; localization and representative
transport yield the displayed square. It is attached to
`Sheaf.Algebra.Homology.RingedSliceHomSourceShift`.

`lem-coef-signed-single-dual-restriction` packages the evaluation, symmetry and
single-dual source-shift comparisons for the fixed derived restriction functor.
Its theorem is proved, and includes the natural coefficient transport definition.
It is attached to `Sheaf.CategoryTheory.RingedSiteSignedDualRestriction`.

Both nodes inherit the item's chapter and unit and identify the blueprint ancestor
and proof paragraph they serve. Searches of the blueprint, source library and three
Mathlib search kinds found no matching normalized restriction-and-source-shift result.
The existing main node's proof and proof dependencies are updated to the Lean argument.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
