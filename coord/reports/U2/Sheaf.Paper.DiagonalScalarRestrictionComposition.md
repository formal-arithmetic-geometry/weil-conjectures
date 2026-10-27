## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.scalarRestriction_comp` in
`Sheaf.Paper.DiagonalScalarRestrictionComposition`, preserving its complete signature and
both public imports. Added private helpers for nonflat restriction acyclicity, exact-derived
composition factors, ordinary coefficient-square composition, and full-unit horizontal
composition. All proof imports are private. Updated the existing node's proof route and
proof dependencies; no shared interface changed.

The new private imports are
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`, and the full private
interfaces of `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`,
`Sheaf.CategoryTheory.CompactSupportIdentityCalculus`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`.
A source import-closure comparison adds only `CompactSupportIdentityCalculus` to
`TargetsCheck`'s closure; that module is already sorry-free. No other source module
is added to the closure.

Validation: the complete module compiled on the server within 60 seconds
(31.1 seconds). The delivery command performs the final compile and preflight.
The target signature is unchanged, no Lean line exceeds 100 characters, and
profiling options have been removed.

The acyclicity argument uses the existing localized-Hom theorem
`CategoryTheory.isIso_map_of_adjoints`: scalar extension is tested on K-flat complexes,
and geometric inverse image on K-flat resolutions whose images are K-flat. Naturality
then makes the supplied derived unit invertible on restricted K-injectives. The existing
`derivedCoefficientComparison` constructs normalized squares for arbitrary universal models.
For composition, cancel the invertible source unit on K-injective representatives and
use all three full-unit equations, including the equation on a restricted complex which
need not be K-injective. The existing `push_pasting_canonical` then supplies the mate law.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.scalarRestriction_comp`
(node `lem-diagonal-scalar-restriction-composition`).
Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No split-off obligations, axioms, or changes to definitions or statements.

## No longer needed

The proof does not need `lem-sfb-module-pullback-preserves-kflat`: it uses the smaller
family of K-flat test resolutions whose inverse images are K-flat, obtained from flat
object preservation. It does not invoke the global preservation-of-K-flat-complexes
instance. A local test-map instance uses geometric exactness explicitly.
It also does not use canonical-model transport
(`lem-diagonal-canonical-right-derived`) or the named derived push/pull functors
(`sk-def-sfb-module-derived-pushpull`) or the derived geometric adjunction
(`def-sfb-module-derived-pushpull-adjunction`); it works with the given models and ordinary
adjunctions directly. These are removed from this node's direct proof dependencies.
Original imports removed: none. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically compatible with the statement, but its proposed
transport through canonical models and its coextension argument are unnecessary.
Full-unit normalization on every complex, rather than only K-injectives, lets the
composition proof evaluate the second square on a possibly non-K-injective restriction.
The nonflat case does not require scalar restriction to preserve K-injectives.

Reused the proved generic helpers from
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`, and
`Sheaf.CategoryTheory.CompactSupportIdentityCalculus` as formal categorical tools.
The flat-object input comes from `new-proetale-inverse-image-module-flat`.
The unit route is unchanged. Identity maps, empty schemes, zero coefficient rings,
and arbitrary unbounded complexes require no additional hypotheses.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
