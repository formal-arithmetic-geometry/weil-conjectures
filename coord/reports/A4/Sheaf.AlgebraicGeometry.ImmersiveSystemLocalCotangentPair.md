## What changed

Replaced the hole in `AlgebraicGeometry.immersiveSystem_local_cotangent_pair` by a proof
from source first-jet realization. The proof establishes closedness and rationality of the
points, obtains cotangent surjectivity from the existing rational unramified criterion,
transports a free generator using adjunction uniqueness, computes the pulled-back
coefficients, lifts arbitrary cotangent classes, produces a nonvanishing section by
approximating 1, and selects two independent classes using the finrank bound.

Added `Sheaf.AlgebraicGeometry.ImmersiveSystemSourceFirstJets`, containing the remaining
source geometric step. It concerns a closed point of X and a prescribed local frame;
it has no etale scheme T, etale map, dimension bound, affine neighbourhood construction,
nonvanishing-section choice, or independent pair. Its conclusion is congruence modulo
the maximal-ideal square. The parent proof performs the etale transport and all choices
in Lean. This is a decomposition, not a complete proof of the geometric input.

All existing declaration signatures and public imports are unchanged. New proof imports
are private. Updated the item node's proof, proof dependencies and proof origin. The new
module imports ideal operations for its congruence statement; it needs neither an etale
morphism import nor the cotangent-space API.

## Proved and sorry left

Closed the one existing hole in `AlgebraicGeometry.immersiveSystem_local_cotangent_pair`
(node `lem-zl-immersive-system-local-cotangent-pair`) by decomposition.

Added one hole: `AlgebraicGeometry.immersiveSystem_source_first_jets`
(node `lem-zl-immersive-system-source-first-jets`). Its complete geometric proof in words
is in its docstring and DAG node. Net holes closed minus added: zero.

Both private helpers, `closedPoint_residueMap_bijective` and
`tensorUnit_freeGenerator`, are proved, with no holes. There are no other new holes
and no holes inside definitions.

Validation: `lcompile.py --all` compiled both delivered modules cleanly, in 4.0 s
and 9.8 s respectively. The existing theorem signature and public-import list were
compared verbatim to the repository originals and are unchanged.

## No longer needed

No modules are withdrawn and no existing public imports are removed. No unit route is
bypassed. The projective chart and immersion dependencies remain needed by the new
source first-jet lemma; they have not been pruned from the argument.

The item's proof no longer directly uses
`lem-weil-pbc-invertible-generating-sections-fibre`,
`def-weil-pbc-morphism-to-projective-space-by-sections`,
`lem-weil-pbc-projective-space-standard-charts`, or `def-weil-closed-immersion` for its
geometric step: these dependencies are now on the source first-jet node instead.
They are still transitively needed. The source `PointCount` closed-point theorem handles
local finite type without assuming the whole scheme quasi-compact; the proof does not
import `Sheaf.AlgebraicGeometry.ClosedPointField`.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide projective charts, section ratios and the rational
unramified cotangent criterion, but none states that the actual coefficients of the
given immersive system realize the first jets at a source point. This is the remaining
geometric bridge, now isolated with a precise congruence statement. Existing
`BertiniSingularFibreEquations` assumes smoothness and does not prescribe its surjective
linear map as the coefficient evaluation map, so it cannot supply that bridge here.

The source first-jet statement was checked for an empty X and zero coordinate family
(vacuous or impossible generation), zero-dimensional source points (constant jets),
singular closed source points (immersion still surjects on local rings), arbitrary local
frames (unit change preserves jet surjectivity), and positive characteristic (no division
by characteristic is used). The original theorem's statement was not changed.

## New nodes

`lem-zl-immersive-system-source-first-jets` is the source immersion step of paragraph 3
of the latest finite-cover Bertini proof. Generation chooses a nonzero basis section;
projective ratios and the immersion give cotangent spanning. Constants and linear
combinations realize all jets modulo the maximal-ideal square, in any prescribed frame.
The remaining etale transport, local coefficients and independent-pair choice are proved
in the parent. LeanSearch, LeanFinder, Loogle, Mathlib grep and DAG/blueprint searches
found no applicable existing declaration. No statement or definition change record is
needed because all existing signatures and definitions are preserved.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
