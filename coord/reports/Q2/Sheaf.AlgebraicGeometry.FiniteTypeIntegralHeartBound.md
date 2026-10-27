## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeIntegralHeart_boundedAbove`
in `Sheaf.AlgebraicGeometry.FiniteTypeIntegralHeartBound`, keeping its statement,
universes and public imports unchanged. No other existing Lean module was changed.
Updated only this item's node proof, proof dependencies and proof origin.

The proof constructs an isometric ring equivalence from the given normed closed
unit ball to the spectral integer ring after universe lifting. Postcomposition on
continuous functions gives the condensed coefficient isomorphism. Restriction of
scalars preserves constructibility and commutes with single complexes and derived
direct image. The existing internal constant-model comparison supplies the input
constructibility needed by the integral residue criterion.

For the spectral integral coefficients, the residue criterion gives completeness
and a bounded constructible residue of finite Tor amplitude. The canonical mate
in `internal_integral_direct_image_limits` is invertible and direct image preserves
completeness. The finite internal-etale realization descends the residue input,
and the existing source theorem
`Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType` bounds
its image. Over a field every stalk is flat; bounded devissage gives finite Tor
amplitude. The converse residue criterion gives the integral bound, which reflects
back through the exact, faithful coefficient equivalence.

All auxiliary declarations are proved and private. The local small-site instance
pins the intended universe; otherwise an imported priority-4000 private instance
leaves an unsolved maximum of universe metavariables. No transparency option is
disabled. Zero objects, empty schemes and unordered initial interval witnesses
are covered; intervals are enlarged with min/max before realization.

The server compiler accepted the complete proof without warnings in 33.5 seconds.
The final delivery performs its compile and mechanical checks again. The node's
new dependency edges were checked for paths back to this item; none were found.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeIntegralHeart_boundedAbove`
(node `lem-sfb-finite-type-integral-heart-bound`).

There are zero `sorry` occurrences in the delivered Lean file. No holes were added,
no statements were split off, and no other module's proof was replaced or changed.
This is a proof from existing library declarations, including whatever remaining
proof obligations those declarations already have.

## No longer needed

The original module had only its two statement imports; both are retained.
The following planned dependencies are unnecessary for this item's proof and are
not imported or cited by its updated node:

- `lem-kun-dimension-finite-type`, module
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the existing
  classical finite-type direct-image theorem supplies a bound without choosing a
  dimension bound here.
- `lem-sfb-normed-coefficient-realization`, module
  `Sheaf.Paper.NormedCoefficientRealization`: use an explicit isometry and ULift;
  no embedding into an algebraic closure or finite intermediate field is needed.
- `lem-sfb-integral-constructible-completion-bridge`, module
  `Sheaf.Paper.IntegralConstructibleCompletionBridge`: use the internal residue
  criterion on the actual spectral integer ring directly.
- `lem-sfb-integral-ambient-tower-comparison`, module
  `Sheaf.Paper.IntegralAmbientTowerComparison`: completeness and the actual
  reduction/direct-image mate are already supplied by
  `internal_integral_direct_image_limits`.
- `lem-sf-integral-direct-image-constructible`, module
  `Sheaf.Paper.SfIntegralDirectImageConstructible`: realize just the finite residue
  image and apply the converse internal criterion, avoiding the finite-stage
  integral presentation.

The original Mathlib noetherian dependency remains in use. These are dependencies
pruned from this argument, not claims that the modules have no other consumers.
No module was withdrawn and no source-library declaration was removed.

During implementation, removed the exploratory proof imports of
`Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage`,
`Sheaf.Paper.IntegralIndConstructibleHeartClosure`, and
`Sheaf.Paper.IntegralHeartConstructibleModuleComplete`: the proof only needs the
general limits/criterion interfaces, the elementary zero-model construction, and
explicit coefficient-lifting calculations. Also removed the redundant explicit
import of `Sheaf.Paper.ContinuousCoefficientModuleEncoding`, already publicly
reexported by the continuous-encoding comparison.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The planned
uniform positive-level integral tower bound is unnecessary for this existential
upper bound: the first residue field, preservation of completeness, and the
existing converse integral residue criterion suffice. The imported classical
finite-type theorem is acyclic here; its field-valued bounded image also has
finite Tor amplitude by flatness and bounded devissage.

The unit `sk-prop-open-coefficients` has no node in its `realized.statement` or
`realized.steps` lists. Its integral completeness/reduction/etale-comparison route
is retained; this proof does not bypass a realized unit step. No new nodes,
shared-interface changes, forced adaptations or change records are needed.

`coord/delivery-errors.md` currently has no section I; its available stage-1 and
stage-2 sections were checked where applicable. No second-reader section is
included, as instructed in the dispatcher brief.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
