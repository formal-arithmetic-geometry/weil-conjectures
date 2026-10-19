## What changed

Retained the earlier attempt's proofs of `closedSupport_triangle` and `closedSupport_fiber`,
and repaired the derived-unit comparison in the private `supportOpenUnitComparison` helper.
The triangle uses the proved source-library recollement API, derived full faithfulness,
and joint detection of zero objects by closed and open restriction. The fibre comparison
uses the rotated mapping-cocone triangle and the canonical termwise-unit comparison.
All existing public signatures, definitions, instance attributes, and public imports stay
unchanged. Three proof-only source-library imports supply the generic tools.

## Proved and sorry left

Two original holes closed: `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_triangle`
and `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_fiber`, both belonging to
`det-lem-formal-closed-support-adjunction`. No holes added and none split off.

One original hole remains, unchanged and already marked STATEMENT-DISPUTED:
`AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_lowerStarExact`
(`det-lem-formal-closed-support-adjunction`). Its unrestricted signature omits the
quasi-compact open-complement hypothesis of the node and source. The valid exactness
needed in the triangle and fibre proofs follows locally from the proved support adjunction,
which has the complement hypothesis. This is not counted as proving unrestricted exactness.
The fresh direct compile succeeded on resumption in 13.0 seconds with no warnings.
The required delivery dry run also passed: commit `7f82bccf3f`, review class CODEX
(node proof update and an existing disputed statement). Two earlier requests failed
at the server transport layer, but verification subsequently succeeded.

## No longer needed

No existing imports removed. Removed the obsolete `lem-weil-pbc-complex-ses-triangle`
entry from the node's `tool_uses` approvals, preserving the other entries in order. The source-library recollement proof replaces the planned
short-exact-sequence construction: `lem-weil-pbc-complex-ses-triangle` and its implementation
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact` are not needed by these proofs.
There is no new dependency on degreewise-injective replacement, a functorial resolution,
or local cohomology calculations of the shifted mapping cone. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox's attempted narrowing of `closedSupport_lowerStarExact` was not a
proof of its original statement. It also removed an instance required by unrestricted
public definitions `closedPullbackDerivedAdjunction` and `closedSupportProjection` in
`Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom`, held by X6. Repairing those
signatures is prohibited by the forced-adaptation rule for another group's module.
The explicit external use in `ConstructibleExtContinuityStratum` alone did not capture
these implicit instance consumers. Restored the original public interface and left the
already disputed theorem unchanged. No consumer adaptation or change record is required.

The cited Stacks source `literature/stacks-project/proetale.tex`,
`lemma-closed-immersion-complement-retrocompact-exact`, explicitly assumes retrocompact
open complement; `lemma-finite` assumes finite and locally finitely presented. Neither
proves the unrestricted helper. The node itself already has the correct complement
hypothesis. The two remaining clause-(4) statements can be proved using existing generic
recollement lemmas without the planned degreewise short exact sequence. This retains the
unit's open/closed localization and adjunction route.

Stacks also explicitly cautions at the start of its section "Closed immersions and
pro-etale sites" that general closed direct image may fail to be exact. Accordingly
there is no justified proof of the unrestricted instance to substitute for its hole.
Its repair requires coordination of the consumers held by another group; the delivery
closes the two valid remaining clause-(4) holes and preserves this existing dispute.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
