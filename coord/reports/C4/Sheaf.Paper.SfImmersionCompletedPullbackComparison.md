## What changed

Repair of reviewer C-ddea0's return of ddea060962c.

2b/A3: merged strictIso_exists through roosRlim verbatim from CoreB back into
SfImmersionCompletedPullbackComparison, including every private helper. Restored
the original strictIso_exists docstring, the five [-instance] lines, all three
original local irreducible declarations, and Elab.async false. Removed the
unpublished CoreB module. The item publicly imports CoreA and also uses
import all CoreA for its original private ordinary_transport_eq helper.
The strict/Roos block now has its actual proof imports in the item.

D1: removed the unpublished lem-sf-immersion-completed-pullback-models node.
Restored all 21 CoreB public names to the item node's lean.declarations, alongside
its two theorem names. Every use of that duplicate node was replaced by the
eight actual dependencies specified by the reviewer. proof_deps is exactly
the union of proof-step uses, and stmt_deps is unchanged from current main.
The existing definition owner is not changed or duplicated by a new node.

Retained CoreA and its coefficient node, the finite-interval module and node,
and every new proof from the returned head. All 44 original public signatures
and all existing definition bodies agree with current main. The only original
public proof body changed is immersion_completed_pullback_comparison. No
source-library file changes. The remaining CoreA extraction allows the finite
obligation to be imported without an import cycle through its consumer.

Change record: coord/changes/C4-immersion-completed-pullback-extraction.md.

Final lcompile --all passed for all three delivery modules and all ten live
direct importers, individually in import order. The merged item took 33.9 seconds;
the longest live importer took 30.6 seconds. All temporary consumer copies were
removed, and no consumer adaptation is delivered. Five other initial source
paths were quarantined by the running global build during the check; their
temporary copies and timing experiments are excluded from this packet. Their
quarantine archives and nodes are untouched.

## Proved and sorry left

The original hole in
AlgebraicGeometry.Scheme.ImmersionCompletedPullback.immersion_completed_pullback_comparison
is closed by a decomposition. Its Lean proof includes exactness, product
preservation, transfer from represented complexes to arbitrary derived towers,
coefficient completeness transport, invertibility of the actual strict unit,
and assembly of integral constructibility with the original uniform bounds.
These proofs are retained unchanged from the returned head.

The item's one original hole remains:

- AlgebraicGeometry.Scheme.ImmersionCompletedPullback.rlimComparison_roos,
  node lem-sf-immersion-completed-pullback-comparison, unchanged from current main.

The packet adds one smaller named theorem hole:

- AlgebraicGeometry.Scheme.ImmersionCompletedPullback.finite_reduction_preservesConstructibleInterval,
  node lem-sf-immersion-finite-reduction-interval, in SfImmersionFiniteReductionInterval.
  It concerns one finite reduction without completeness or uniform-in-level
  assumptions; it concludes neither completeness nor integral constructibility.

There are two holes across the three delivery modules: one retained original
and one split off. Closing one original hole and adding one lower hole is a
decomposition with net zero holes, not an unconditional proof. CoreA is proved,
and every restored strict/Roos construction is proved. The new finite theorem's
source and full proof in words remain in its docstring. Empty intervals, zero
complexes, empty schemes and identity immersions remain covered.

## No longer needed

The returned packet's unnecessary SfImmersionCompletedPullbackCoreB module and
lem-sf-immersion-completed-pullback-models node are removed as requested. They
were unpublished additions, absent on current main; no deletion manifest for
an existing library path is needed. Their mathematics and declaration records
are restored to the item, rather than removed from the library's argument.

Direct proof imports of MapDerivedCategoryMate, WeilCompletedTensorReflector
and RoosComparisonHorizontalCoherence remain unnecessary: the existing
normalization APIs supply the generic facts used here. No adopted-source
declaration is removed. The originally proposed integral-detailed-finite-reduction
lemma is unused because its Noetherian hypothesis does not cover arbitrary
schemes in the assigned statement; the single finite-level split records the
needed coefficient comparison and inverse-image step. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified the unnecessary CoreB split and duplicate
ownership node. The original monolith and the reviewer's recombination both
compiled within 60 seconds, so this extraction was unjustified. Both return
points are repaired directly, retaining the new proofs and the useful CoreA
extraction. No statement, binder, universe or definition is weakened.

The earlier retained draft had regressed roosRlim_exists and replaced
termwiseLimitIso_eq by a tautology. Their original proved bodies remain restored;
the repair moves those bodies verbatim into their original item. The obsolete
unqualified generated attachments and redundant equation-only split remain
excluded from the packet.

## New nodes

lem-sf-immersion-completed-pullback-coefficients is retained unchanged, recording
the 21 coefficient/finite normalization declarations in CoreA and their proved
unit, transition and projection compatibilities. CoreA remains the separate
coefficient interface required by the finite-level obligation.

lem-sf-immersion-finite-reduction-interval is retained unchanged. Its proof plan
identifies the finite coefficient presentations, applies exact finite inverse
image to the constructible strata and constant models, and preserves vanishing
outside the supplied interval. The final theorem applies it to the source's
uniform interval and then to the separately specified interval.

Change record: coord/changes/C4-immersion-completed-pullback-extraction.md.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
