## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_lowerTail`
in `Sheaf.Paper.ContinuousAlgClProperLowerTail`, preserving its entire statement,
public import, and existing declarations. Added the proof-only import
`Sheaf.Paper.QcqsProperHullTailBound` and updated the item's DAG proof and dependencies.

The existing `exists_uniform_lowerTail_bound_of_isProper` theorem applies with base
`Y`, proper structural map `𝟙 Y`, and proper morphism `p`. The standing field hypotheses
make `Y` qcqs. The coefficient is exactly the sixth admissibility clause, via its
identity monoid-object isomorphism; no finite-subextension coefficient is substituted.
Choose its uniform constant `c`, put `a = q - c`, and use `DerivedCategory.isLE_iff`.
For `r > q - 1`, integer arithmetic gives `a + c ≤ r`. Finally map the standard
`truncLEIsoTruncLT (a - 1) a` by the same total derived pushforward and transport
`IsLE (q - 1)`. The pushforward wrapper unfolds definitionally to `lowerStar`'s
`rightDerivedFunctor`.

Validation: the item compiled cleanly on the prescribed compile server (4.9 seconds).
The import-direction check accepts the new import, and a traversal of statement,
proof and step-use dependencies found no reverse DAG path from the general tail
bound to this item. The unchanged generic theorem and item use exactly the same
ordinary ambient module category and `localizingClosureProEtale`. The proof covers
zero objects, empty schemes, negative cutoffs and `c = 0` without case exclusions.

Searches run: Lean Finder for uniform proper lower-tail bounds returned generic
truncation/support results; Loogle for `DerivedCategory.isLE_iff` found the exact
cohomological criterion; grep for `truncLEIsoTruncLT` found the standard comparison.
Repository searches found the already-proved general qcqs hull-tail theorem and
confirmed its full continuous-map coefficient clause. No new mathematical result
was needed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgCl_proper_lowerTail`
(node `det-sf-comp-continuous-algcl-lower-tail`).

No `sorry` remains in the item. No holes were added and no statements were split off.
The proof uses existing library theorems with their existing dependencies, as intended
in stage 3; it does not claim those dependencies have no transitive holes.

## No longer needed

The direct planned proof dependencies `sk-lem-proper-heart-bound`
(`Sheaf.Paper.ProperHeartBound`) and `det-ambient-ind-derived-sums`
(`Sheaf.Paper.AmbientIndDerivedSums`) are replaced by
`lem-sfb-qcqs-proper-hull-tail-bound` (`Sheaf.Paper.QcqsProperHullTailBound`).
Their displayed interfaces concern finite coefficient subextensions and the
finite-subextension-valued algebraic closure, so a separate adaptation of them to
all continuous maps is unnecessary for this item. The general theorem already
performs the localizing-hull and unbounded-tail argument for the exact coefficient.

No existing imports were removed: the existing public import provides the statement's
interface. The sole added private import is used. No module is withdrawn or claimed
to be globally pruned: the old dependencies can still be needed by other declarations
and through retained imports.

## Where the brief, the DAG or earlier work was wrong

The original proof plan names heart and ambient-ind declarations whose signatures
use the finite-subextension-valued algebraic closure, while this item's coefficient
is the full continuous-map ring. The existing general qcqs tail theorem includes
both coefficients as separate admissibility clauses and gives the requested result
directly. This avoids asserting an identification between those rings and leaves
the target, item statement, unit route, definitions and all consumer interfaces
unchanged. The general theorem belongs to the same recorded unit.

The rework row was checked before copying: although it records the earlier quarantine,
the item source is currently present at its normal Lean path. The delivery fills that
source's hole and preserves its Lean attachment and mathematical role; it neither
withdraws the archive nor treats quarantine as evidence of redundancy.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
