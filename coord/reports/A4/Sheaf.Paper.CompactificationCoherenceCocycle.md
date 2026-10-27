## What changed

Repair of the return for head `a0dcd30cf28`: its proof passed independent review, but
landing rejected the basename-only reviewer fix for the change record. The record is
included at `coord/changes/A4-canonical-refinement-transport.md`; its delivery path is
now explicit inside the record. Reviewer edits must use this full repository-relative
path. The retained proof and identity adaptation are preserved. Node metadata is refreshed
from current `sheaf-dag`, retaining only this delivery's owned changes, and the delivery
command prepares the replacement commit on the freshly fetched branch.

Replaced the hole in `Sheaf.Paper.CompactificationCoherenceCocycle` by the general-qcqs
boundary detection argument and explicit common-refinement cancellation. Theorem signatures are unchanged. The refinement component now uses the provably equal
derived `lowerStarCongr` transport to avoid a kernel reduction timeout. The only extra access to private declarations is
`import all Sheaf.Paper.CompactificationRefinementLocalizing`, used for the existing,
unrestricted normalization and composition proofs. The definition change is recorded in
`coord/changes/A4-canonical-refinement-transport.md`; all six current consumers compile.

The component composition proof transports the existing direct-image compositor coherence
through the structural triangle equalities; naturality follows from the open adjunction.
The comparison family is constructed from the actual canonical refinement components.

The retained attempt compiled the final module through `lcompile.py` in 22.0 seconds
and checked all five direct consumers then present. The resumed current-source check
compiles the item and adapted identity module with no diagnostics (50.6 seconds reported).
The current downstream scan also finds `Sheaf.SixFunctors.ScalarSixCompactSupport`.
All six current consumers compile against the item in the renewed validation, with exit
code zero and no diagnostics. The compiler automatically included eight unpublished
scalar-support dependencies in its private overlay.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.compactification_coherence_cocycle`.
There are zero holes left in the item or adapted identity module, zero added holes,
and zero split statements. The identity adaptation closes no additional holes.
Its proof depends on the existing named boundary-vanishing theorem, whose own proof is
outside this item. No definition contains a hole or arbitrary chosen witness of an
unproved existence theorem.

## No longer needed

The separate `lem-sfb-normalized-open-refinement-coherence` and
`lem-sfb-identity-open-derived-restriction` nodes are unnecessary for this proof: the
canonical refinement-data module already has the required mate calculations as complete
private proofs. Accessing these proofs avoids identifying a second normalization of the
same maps. The finite-family clause of common dense refinement is unnecessary: two
successive pairwise common refinements supply the triple used for the cocycle.

The field-restricted proper/open interchange is unnecessary; the general-base
boundary-vanishing statement and open/closed detection apply directly. Existing public
imports are preserved. Removed proof imports:

- `Sheaf.Paper.ProEtaleProperOpenInterchange`: replaced by general-qcqs boundary vanishing.
- `Sheaf.Paper.CartesianCoefficients`: no direct use in the proof.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: no direct use.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`: supplied instead by the
  recorded module compositor coherence.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`: already in the
  public import closure of the canonical refinement-data module.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`: duplicated
  in the old header; neither copy is used directly.
- `Sheaf.Compactification.BoundaryRefinement`: already public through refinement data.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` and
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`: already in the
  preserved public import closure.

No module is withdrawn. These removals do not assert that the listed modules have no
other consumers.

## Where the brief, the DAG or earlier work was wrong

The returned landing failed on the path of a reviewer fix, not on the Lean proof or
the inclusion of the record: the record belongs under `coord/changes/`, and a bare
basename is not its repository path. No compiler failure was reported for that return.

The file's old proof sketch invokes proper/open interchange without the field hypotheses
of its published theorem. The current reviewed DAG already corrects this issue by using
qcqs proper/open boundary vanishing. The proof follows that corrected route.

The rework record retains the item in a quarantine archive, but the current source file is
present and agrees with that archive. It is preserved and proved, not withdrawn.

Proof-only import-all access reuses the existing unrestricted mate lemmas without
changing the refinement module or adding a public API.

The retained refinement-component node had two citations in its proof step but an empty
`proof_deps` list. The resumed packet makes that list agree with the proof-step citations.
The current source scan has seven users of the component, including the item itself;
the change record now includes the newly present scalar-support consumer.

## Forced adaptations

`Sheaf.Paper.CompactificationRefinementIdentity` (unclaimed) fails unchanged against
the new definition at its line 217: the `change` tactic expects the former functor
`eqToIso` transport and does not match the derived `lowerStarCongr` component. Before
that existing `change`, the adaptation unfolds only `compactificationRefinementComponent`
and rewrites its final natural-transformation hom using the module's existing
`RefinementId.derive_eqToIso`. Its signatures and remaining proof stay unchanged.
The original consumer failure was reproduced in the compiled validation set; the
adapted consumer passes in that same set.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
