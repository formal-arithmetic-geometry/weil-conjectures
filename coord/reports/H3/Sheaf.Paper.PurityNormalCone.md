## What changed

Proved all four original holes with their signatures unchanged. The kernel inclusion
uses the existing normalConeToQuotientSpec factorization and its kernel equality;
the retraction identity is lift_fac followed by the retraction equation. The affine
chart is the relative-gluing chart composed with rees_associatedGraded_chart; the
degree-zero formula proves compatibility with its structural ring map. The global
comparison retains the projection and augmentation conjuncts of the already proved
stronger reesConeComparison_exists.

The projection, its kernel lemma and its retraction identity now live in the new
foundation module Sheaf.Paper.PurityNormalProjection. Their existing names,
signatures and defining term are unchanged and publicly reexported by the item.
ReesConeNormalization and ConormalConeHomExt replace their overly broad public
imports by the foundations they actually need. This removes the import cycle
between the item and normalized existence. PurityNormalBundle itself is untouched;
no regular-immersion proof was split or moved. No adopted source-library file changes.

Updated the existing def-pur-normal-bundle attachment to the projection foundation,
which publicly reexports the unchanged regular-bundle construction. Its six original
steps stay. Updated pur9-def-normal-cone to the publicly reexporting item and added
the affine and global presentation-comparison steps. No node statement changes,
new node, or bypass of a blueprint unit occurs.

Change record: coord/changes/h3-purity-normal-projection-foundation.md.

Repair of the return for delivery head 90b838f72: added the missing Users rows for
Sheaf.Paper.AmbientDiagonalPurityBaseChange and
Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase. Both consumers are quarantined in
the current source tree, listed in coord/rework.tsv, and unclaimed. Checked their
preserved sources: DiagonalNormalized uses purityNormalProjection in its
projection condition, and the general-base diagonal proof applies
purityNormalProjection_eq with pullback.diagonal_fst. Identical signatures and
the item's public reexport preserve these uses without source adaptations. The
quarantine sources and attachments are retained; neither is withdrawn.

Repair validation: lcompile.py --all compiled all six sandbox modules successfully
with no diagnostics against the current server build. The item compiled in 5.0
seconds and normalized existence in 9.3 seconds. All six sources have zero sorry
tokens and satisfy the 100-character Lean line limit.

Validation: all six modules of the revised dependency chain compiled without
warnings: ConormalConeHomExt, PurityNormalProjection, ReesConeNormalization,
ConormalConeZeroSectionPullback, ReesConeNormalizedExistence and PurityNormalCone.
The zero-section module is included in the sandbox only to rebuild its compiled
dependencies; it has no source diff. The delivery check encountered a 60-second
timeout rebuilding normalized existence. Profiling found expensive rewriting and
definitional comparison. Its private affine-chart and glued-sheaf isomorphisms now
stay behind their proved representative/chart APIs, and the representative proof
uses congrArg and trans instead of rewriting through the chosen equivalence.
Broad simplification in affine naturality is restricted to its required equations.
These changes preserve every public signature, definition and proof route. Consumer names
and signatures were checked using downstream.py and source searches. The two
comparison theorems have no current Lean callers; all projection callers retain
the old public import interface. deliver3.py performs the final compilation and
axiom checks of the packet.

## Proved and sorry left

Closed four original holes:

- AlgebraicGeometry.Scheme.Hom.purityNormalCone_kernel
- AlgebraicGeometry.Scheme.Hom.purityNormalProjection_eq
- AlgebraicGeometry.Scheme.Hom.purityNormalCone_affineChart
- AlgebraicGeometry.Scheme.Hom.purityNormalCone_comparison

Added zero holes. Split off zero unproved statements. No sorry remains in the item,
the new foundation, or any adapted module. This is a proof from existing proved
interfaces, not a decomposition. Imported foundational results elsewhere in the
library retain their existing proof/axiom status.

## No longer needed

Removed these private imports from the item:

- Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
- Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks
- Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
- Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension
- Sheaf.Paper.PurityVectorBundleZeroSection
- WeilConjectures.RingTheory.RegularSequenceConormal
- Sheaf.RingTheory.RegularSequenceGradedPolynomial
- WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
- WeilConjectures.AlgebraicGeometry.AffineConormalSections

Their regular-immersion argument remains needed in the unchanged
PurityNormalBundle and the six retained def-pur-normal-bundle steps. Thus no node
or module is globally withdrawn or declared unnecessary. The item no longer
repeats that argument. ConormalConeHomExt needs only PurityNormalBundle;
ReesConeNormalization needs only the bundle and projection foundations, not either
presentation-comparison theorem. Both drop their public PurityNormalCone import.
The new chart and normalized-existence proof imports are private.

## Forced adaptations

(Added by the reviewer.) No module held by another group is adapted; the adapted modules
are unclaimed. ReesConeNormalization and ConormalConeHomExt drop their public
PurityNormalCone import (forced: ReesConeNormalizedExistence imports both, and the item now
imports ReesConeNormalizedExistence, so keeping it would be an import cycle).
ReesConeNormalization.coneAlgebraIso and two private lemmas of
ConormalConeZeroSectionPullback carry a `first | <live proof> | <stale-build proof>` so they
compile both against the stale published VectorBundleZeroSection.olean (chosen
antiEquivalence) and against the live source (concrete antiEquivalence); the delivered
versions compiled only against the stale build. See the change record. ReesConeNormalizedExistence
receives proof-performance edits only (private defs made irreducible after their API lemmas).

## Where the brief, the DAG or earlier work was wrong

The existing normalized existence theorem already proves more than the global
comparison requested here, but its public import of this item hid a dependency
cycle. It uses only the projection foundation. The original node attachment also
put the regular-bundle construction, projection foundation, and comparison in one
layer despite their different dependencies. Reattaching the two existing nodes
and moving only the small projection interface repairs that layering without
changing any mathematical statement or construction. The source-library
factorization and the associated-graded chart already supply the other needed
arguments; no new algebraic equivalence or geometry was required.

The previous Users enumeration covered the live Lean tree but omitted two
quarantined consumers. The return correctly requires both preserved consumers in
the change record even while they are absent from lean/; both are now included.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
