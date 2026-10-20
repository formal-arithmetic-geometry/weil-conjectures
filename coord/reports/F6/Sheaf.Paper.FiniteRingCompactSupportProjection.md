## What changed

Proved `AlgebraicGeometry.Scheme.isIso_finiteRingCompactSupportProjection` from the existing
finite-ring constructible-origin theorem, the unbounded direct-image comparison, the etale
proper torsion projection formula, and the published open projection isomorphism. The theorem's
signature remains unchanged. The map module factors the same specified canonical arrow through
a generic realization API, with the existing abelian structure and derived-category model
stored once; this avoids repeated nested-proof conversion.

The proof works in fixed scalar coefficients, exactly where the specified projection is defined,
and transports its invertibility through the canonical intrinsic realization. Private proved
helpers identify the two derived-adjunction presentations, identify the unbounded comparison
with the mate in the categorical projection transport theorem, assemble the proper projection
on objects of etale origin, transfer the origin isomorphisms through realization, and assemble
the compactification formula for a general coefficient category. These abstractions keep
Lean from unfolding the concrete module-sheaf constructions during categorical transport. The
finite-field coefficient arithmetic is proved separately before specializing the proper formula.
No adopted source-library file is changed.

Verification: the actual map and theorem modules compile cleanly (8.1 s and 20.0 s).
The unchanged consumer modules `ConstructibleProjectionMates`, `SfExchanges` and
`SfProEtaleProjectionFormula` also compile against the delivered definitions.
Both delivery modules have zero sorry tokens; the theorem signature and both public
import lists agree verbatim with the repository versions.
An additional single-file check of unchanged `CompactSupportProjectionFormula` reaches
the 60-second limit, as does the control using the published original map. Its baseline
performance issue is not a forced adaptation caused by this definition repair; its source
is unchanged. The maintainer's global build remains the full consumer-closure check.

The unclaimed module `Sheaf.Paper.FiniteRingCompactSupportProjectionMap` gains the generic
component API and cached canonical interfaces. Its definition change is recorded in
`coord/changes/F6-finite-ring-projection-realization.md` and reopens independent statement review
for its consumers. The original realization functors and the counit-defined projection remain
the ones used to construct the arrow.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.isIso_finiteRingCompactSupportProjection`
(node `lem-sp-finite-ring-compact-support-projection`).

Holes closed: 1. Holes added: 0. No sorry remains in either delivered module (item: 0; map module: 0). No split-off theorem.
The private helpers are proved completely. Existing imported declarations retain their own
proof status; they are not new holes in this delivery.

## No longer needed

The general ringed-topos tensor-pullback and exchange/tensor-coherence interfaces are not needed
by this proof: the source library already proves the corresponding fixed-coefficient tensor
compatibility and categorical projection-mate transport. The proof still uses etale origins,
exact extension by zero, the canonical pullback square, unbounded direct-image comparison,
the proper etale projection formula, and the open projection isomorphism.

Removed direct proof imports from the item (the corresponding results are supplied by the
proved source interfaces already imported):

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`

The two removed DAG proof dependencies (also removed from `tool_uses`) are
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and
`lem-weil-pbc-ringed-exchange-tensor-coherence`.

The map module also removes its obsolete private proof imports; only the ModuleCat
Grothendieck-instance interface remains. In addition to the imports above, these are
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`, and `Mathlib.GroupTheory.Torsion`;
the item still imports and uses these three. No declaration or module is withdrawn, and no
claim is made that the removed direct imports leave the entire targets' import closure: other
modules may still import them.

## Where the brief, the DAG or earlier work was wrong

The stated six-step argument is mathematically sound. Its general ringed-topos interfaces
are unnecessary for the fixed-coefficient presentation used by the actual projection-map
definition. The ordinary bounded-below comparison theorem alone would not suffice because
`j!M0` tensor `p*K0` need not be bounded below; the proof uses the existing unbounded theorem
at both arguments. No finite Tor-amplitude hypothesis is added.

The original map representation repeatedly rebuilds the sheaf abelian structure and the
chosen small derived-category model when components are compared. The map repair names those
existing data and the bifunctor endpoints. Whole-transformation equality, transported through
the invertibility predicate, avoids reducing component projections during conversion.

The fixed-coefficient interfaces use the same `CommRing.toRing` projection in abstract
coefficients and after `ULift`. At the final assembly call, the origin objects and inverse
realization objects are passed explicitly: local aliases otherwise trigger expensive
conversion through the derived functor bodies. These are representation changes only.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
