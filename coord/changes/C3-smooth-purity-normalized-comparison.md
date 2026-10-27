# AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace_from_representing_pairing

## Reason

Prove the native finite root-quotient square and uniqueness of the normalized
comparison determined by a supplied representing pairing. Repair avoidable local
unfolding of Spec while registering the private point-obstruction instances.
This is partial proof work, not a completed construction of smoothTrace.

## Old

All existing declaration signatures, attributes, public imports and non-theorem
bodies in WeilConjectures.SmoothPurity.Defs are the current library version.
The private smoothTrace_from_representing_pairing constructed its comparison by
transposing the supplied pairing and composing with the supplied Tate and target
unit isomorphisms, without stating its uniqueness.
The PointObstruction section registered its three private instance lemmas without
local irreducibility annotations for AlgebraicGeometry.Spec, Over.mk or
ReconstructionResult.

## New

Add the proved private smoothTrace_normalizedComparison_unique. Its complete
statement and proof are in the item. The existing private
smoothTrace_from_representing_pairing uses its existence conclusion. Its original
signature and documentation remain verbatim.

Add the proved private smoothTrace_finiteQuotientSquare, using a private import
of Sheaf.Paper.FinitePuritySourceUnitReduction. The supplied finite-purity square,
naturality at the actual coefficient-unit map, and finite root balancing give
exactly the specified gamma quotient square. No finite-level orientation is chosen.
The new private smoothTrace_normalizedFiniteSystem combines that calculation with
the actual positive finite-system witnesses and the original ReconstructionResult
for the same compactification. It performs all witness extraction inside a proof.

Keep AlgebraicGeometry.Spec locally irreducible only in PointObstruction.
Keep Over.mk locally irreducible for the original three instance registrations,
then restore its semireducibility before the point counterexample. All three
registrations are retained. Keep ReconstructionResult locally irreducible in
Purity and explicitly unfold it to extract its finite-system projection. In a
new FiniteNative section containing only the two new finite proofs, keep
HasDerivedCategory.standard and Functor.leftAdjoint locally irreducible.
Every annotation is section-local; no global reducibility attribute or existing
definition changes. The chosen boundedConstructibleLowerShriek, boundedConstructibleUpperShriek and
boundedConstructibleUpperShriekAdjunction stay locally irreducible throughout
Purity. Elaboration is synchronous. The existing private
smoothPurityMap_of_reconstructed_trace proof names its lifted Tate comparison,
composite and two equations separately; its signature and docstring are unchanged.
The final module compiles cleanly in 45.0 seconds.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SmoothPurity.Defs | C3 | Private proof changes and section-local unfolding control. |
| Sheaf.Targets.SmoothPurityQbar | not queried; unchanged | Identical public interface and definitions. |
| WeilConjectures.PoincareDuality.Poincare | not queried; unchanged | Identical public interface and definitions. |
| WeilConjectures.TraceFormula.Dualizing | not queried; unchanged | Identical public interface and definitions. |
| TargetsCheck | not queried; unchanged | Identical public interface and definitions. |
| WeilConjectures | not queried; unchanged | Identical public interface and definitions. |

These are all direct importers in the current source. No consumer adaptation is
required: no public signature, attribute, import or definition body changes, and
the reducibility annotation is local to a completed section. Target meanings do
not change.

## Status

landed 20261027T103411-L-1067180 2026-10-27 (merge of deliver/C3/WeilConjectures.SmoothPurity.Defs)
