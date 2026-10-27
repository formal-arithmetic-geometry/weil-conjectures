## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.coefficientHeart` by an assembly
of the existing closure, smallness, ordered common stratification, counit filtration,
exact locally closed extension, generic-neighborhood, lisse-descent and curve-complement
results. The Noetherian instance is constructed from the standing hypotheses. The
finite-Tor equality uses the existing localizing-closure theorem in each coefficient
case. Standard cohomology-truncation lemmas give truncation stability. On the dense
open, canonical pullback comparisons and composition of trivializing covers give
lissity; the complement uses the actual reduced induced closed subscheme.

The assigned theorem, its assertion definitions and all public imports stay unchanged.
The complement is constructed explicitly as the vanishing-ideal subscheme through
`heartComplement` and `heartComplementι`, with proved reducedness, closedness and
range; the localization argument then uses its abstract scheme and inclusion.
In the unclaimed `Sheaf.Paper.CoefficientHeartClosure`, normalized the coefficient
expression of `coefficientHeart_closure` to the already existing definitionally equal
`coefficientHeartRingObj` abbreviation. This prevents the consumer's kernel from
repeatedly expanding transported monoid structures while comparing the lisse
stratification clause. Its existing complete proof is retained; no data or instance
changes. The change record lists every direct declaration user:
`coord/changes/C6-coefficient-heart-closure-coefficient-normalization.md`.
Also normalized the unclaimed curve-complement theorem from a bundled condensed
ring to its underlying sheaf and monoid instances. Its proved body changes only
by replacing `Λ.X` with `Λ`; the isolated bundled-to-unbundled localization
conversion previously hit a kernel timeout. The second change record is
`coord/changes/C6-coefficient-heart-complement-coefficient-normalization.md`.

The `all` proof imports expose existing proved private helper APIs for finite-free
models and for pullback, isomorphism transport and locality of lissity. No theorem
about finite-etale pushforward is used. The local irreducibility attributes keep
coefficient pullbacks and extension functors abstract during elaboration, and do
not change other modules' environments. A declaration-local
`backward.isDefEq.respectTransparency` setting ensures elaboration respects these
abstractions instead of unfolding the full functor constructions.

Private definitions give the large constructions small proof interfaces:
`heartFiltrationImage` is the actual counit image, with a proved equality to the
existing filtration step; `heartLissePullback` is the original lisse predicate
on an actual inverse image, with proved composition and cover-locality lemmas.
The former makes the complete filtration assembly compile in about ten seconds;
the latter reduces generic open-cover gluing from a kernel timeout to milliseconds.
These definitions contain their actual data, no postponed proofs. The closed-square
and open-supremum lemmas are proved private glue for the existing descent result.
The actual reduced complement is constructed first and then unpacked through its
proved geometric properties before applying the localization theorem, avoiding
repeated ideal-sheaf reductions in coefficient-module expressions.
Updated the existing node's proof fields.

Added direct proof imports:
- `Sheaf.AlgebraicGeometry.StratificationGenericNeighborhood`
- `Sheaf.Paper.CoefficientHeartCurveComplement`
- `Sheaf.Paper.CoefficientHeartCurveLisseDescent`
- `Sheaf.Paper.CoefficientHeartLocallyClosedExtension`
- `Sheaf.Paper.FiniteEtaleLocallyFreeModels`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.coefficientHeart`
(`sk-lem-coefficient-heart`), one of one original holes.
Added: zero holes. Split off: zero statements. Remaining holes in the delivered
module: none. Both adapted dependencies are also complete, with zero holes.
The complete parent compiles through `lcompile.py` in 17.2 seconds; the normalized
curve-complement dependency compiles in 51.1 seconds and closure in 54.9 seconds. The proof depends on existing theorems whose own proofs may remain
unfinished; these remain independent items, rather than new holes in this delivery.

The assembly handles empty schemes, empty complements, zero sheaves, rank zero,
non-strict filtrations, reducible curves and nonreduced strata. It uses actual
fiber products and does not infer scheme factorizations from point-set containment.

## No longer needed

Removed direct proof imports:
- `Sheaf.Paper.CoefficientHeartCommonStratification`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.CondensedSurjectiveClosedEquivalence`
- `Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
- `WeilConjectures.Mathlib.Topology.KrullDimension`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`

The explicit coefficient-completion comparisons (`sk-prop-sfb-qlbar-colimit-x`)
are not a direct proof dependency: the existing closure and Tor results already
accept the exact specified coefficient sheaves. The standing-setting definition
node `sk-def-sfb-dc-setting` is likewise not needed as a proof lemma; the unchanged
theorem binders supply its hypotheses. The detailed geometry, coefficient
Cartesianity, cover-refinement, universal-homeomorphism and open-closed sequence
results are used through their retained higher-level dependencies, not reproved
or directly imported here. Their modules may still be transitively needed; no
module is withdrawn and no global pruning count is claimed. Every node realizing
a unit step remains on the route, including common stratification, closure,
smallness and filtration.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. Two coefficient-interface normalizations
were needed for compilation: the isolated stratification-clause conversion originally
hit a kernel deterministic timeout; after normalization it checks in 0.216 seconds.
The coefficient object and all mathematical hypotheses and conclusions are identical. The original proof imports did not
include the four newly stated geometric assembly dependencies, although their
DAG declarations were available. The correct conversion for arbitrary exact pairs
uses `ShortComplex.exact_iff_exact_toComposableArrows`; a composable-arrow exactness
proof is not itself a short-complex exactness proof. The dense-open gluing uses
an actual Zariski cover of the supremum open, followed by pro-etale cover
composition. No new nodes are needed. Both coefficient-interface normalizations are
mathematically identical and are documented in their change records.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
