## What changed

Replaced the single hole in
`WeilConjectures.IntegralSystemRealization.integralBasicRealization` by a complete
Lean assembly of its primitive comparisons. The pullback and tensor isomorphisms
are the published normalized model inverses, restricted to the required domains.
The reconstruction-unit proof maps the prime unit from the finite base field to
the scheme, and uses normalized reconstruction and the proved comparison of the
two completeness predicates. Proper and open natural isomorphisms are assembled
from the actual adjunction maps, with their displayed specification equations
proved by reduction and inverse cancellation.

The proper Roos argument is written in Lean: transport the canonical constant-tower
triangle through its finite-image evaluations, using the separately stated successor
transition equation; choose that limit object as the defining direct-image Roos
object. Its comparison can be the supplied isomorphism itself, so cancellation and
`Pi.lift_π` establish every required projection equation. This prunes the proposed
need to normalize the proper conjugate separately against a prechosen Roos object.

Four separate residual mathematical results are stated in their own modules:
normalized ordinary/derived reduction-pullback descent, the proper-image successor
transition equation, invertibility of the actual open-adjunction mate, and whole
compact-support tower normalization. They are distinct portions of the original
argument, not renamed versions of HasBasicRealizations. Each retains the actual
normalizations and maps rather than weakening them to arbitrary comparisons.
Their proof plans and sources are in the docstrings and DAG nodes.

Moved the eight existing specification definitions, with their signatures and
bodies unchanged, to `IntegralBasicRealizationData`, publicly reexported by the
original module. This allows the component theorem modules to state the existing
conditions without an import cycle. The change record `coord/changes/T1-integral-basic-realization-data.md`
documents the exact old/new
blocks and consumer check. IntegralExpressionRecursion is held by T2 and needs no
adaptation. No source-library module changes. No target signatures change.

## Proved and sorry left

Original holes: 1. The body of `integralBasicRealization` now has zero holes.
This is a decomposition, not a net proof of its dependency closure: 1 upper hole
closed and 4 strictly partial obligations added (net -3 before ledger closure effects).
The private helpers primeUnit, primeUnitSections, reconstructionUnit,
restrictedUnitIso, properComparison, properTower and openComparison are all proved.
The definitions in IntegralBasicRealizationData have zero holes.

The four new holes are precisely:

- `WeilConjectures.IntegralSystemRealization.integralReductionPullbackModel`
  (`lem-sf-integral-reduction-pullback-model`).
- `WeilConjectures.IntegralSystemRealization.integralProperTowerTransition`
  (`lem-sf-integral-proper-tower-transition`).
- `WeilConjectures.IntegralSystemRealization.integralOpenMateNormalization`
  (`lem-sf-integral-open-mate-normalization`).
- `WeilConjectures.IntegralSystemRealization.integralSupportTowerNormalization`
  (`lem-sf-integral-support-tower-normalization`).

All remaining sorry bodies are exactly `by sorry` in public named theorems with
sources and full proof plans. Edge cases considered: zero complexes, identity maps,
empty opens, and equal quotient indices. No new nonemptiness assumption is used.
No finite-evaluation faithfulness is asserted; whole-system descent and comparison
are retained where required. Choosing a RealizationModel uses its sectionwise and
whole-representative normalization, not arbitrary existential geometric data.

## No longer needed

No existing modules are withdrawn and no global module pruning is claimed. The
original unit and every parent route remain present. The former proof-only imports
of SemilinearDerivedSections, KFlatResolutionIndependentCoefficients,
CoefficientSystemDerivedComparison, CoefficientSystemUnboundedComparison,
ProEtaleCountableProductsExact, ProEtaleFixedScalarRestrictionDirectImage and
StrictRoosComparison are removed from the item. They are not directly needed by
the assembly. Some remain below the separately stated components, so this does
not claim that their original declarations can be deleted or left unproved.

Original proof Steps 1-2 need no new derivation in this item: the normalized
pullback and tensor model inverses already supply the exact required comparisons.
Their underlying K-flat, quotient-system, Roos and descent dependencies remain
needed by those published model theorems. Original Step 3 is narrowed to the
proper successor-transition equation; normalization against an arbitrary chosen
proper triangle is unnecessary because basicProperTower existentially quantifies
that triangle and its comparison. Steps 4-5 remain as normalized components.
The existing tool approval list is retained, since the components still use the
approved generic tools. No source declaration is removed. The conventions node no longer needs the
scalar-computation theorem as a definition prerequisite; that theorem remains
needed by its actual consumers and is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node plan describes pullback/tensor descent that the published
completed models already contain (also observed in its stage-1 review).
The open-reduction comparison has existentially selected slice data; applying
it to the fixed calculus, fixed ordinary open extension and actual model mate
requires normalized transport, rather than a direct `exact` application.
Similarly, the compact-support conjunct pins the tower and evaluations to the
published choices, and requires a natural map in the strict derived-tower category;
objectwise evaluations alone do not prove it. The four new statements isolate
these actual interface obligations without changing the existing specification.

The definition relocation is structural and preserves mathematical meaning;
it is recorded explicitly rather than claimed as a definition repair.


Returned delivery 791a2e9a6f1: repaired all six reported cycles (the data
statement edge, the data proof edge, and the four component proof edges).
All six paths passed through def-pur-conventions to the scalar-computation theorem.
The conventions now retain the canonical coefficient objects and Weil structures,
while leaving their Frobenius scalar computation to its existing separate theorem.
The already fully constructed PurityFiniteSetting declarations have no dependency
on that computation. Its Lean code, every attached declaration, and the scalar
theorem are unchanged. The 501 direct node consumers are recorded as unchanged
in statement_change.citers and the user table in
`coord/changes/T1-purity-conventions-dependency.md`. This separates data from a
later theorem rather than dropping any needed proof prerequisite.

## New nodes

- `def-sf-integral-basic-realization-data`: the unchanged eight specification definitions.
- `lem-sf-integral-reduction-pullback-model`: normalized reduction/pullback descent.
- `lem-sf-integral-proper-tower-transition`: the proper-image successor equation.
- `lem-sf-integral-open-mate-normalization`: the specified open mate and output unit.
- `lem-sf-integral-support-tower-normalization`: the compact-support tower component.

The first delivery preflight refused two node attachments: the data node stored
a whole definition block instead of its primary signature, and the open node
accidentally began its recorded signature at the word "theorem" in its docstring.
Both attachments now contain the exact declaration signatures. Statement-change
history is included for the explicit data-node reference. Nothing was pushed by
the refused attempt.

Validation: all six delivery modules compile. The final proper-tower refinement
and the unchanged IntegralExpressionRecursion consumer both compile on the server
without warnings (12.8 s and 30.0 s, respectively). The consumer was compiled from
a byte-identical temporary sandbox copy, then removed from the delivery packet.
The definition-body comparison is byte-for-byte for all eight declarations.
The three Mathlib search categories and each proof-dependency union were checked.
The earlier DAG check excluded approved tool boundaries and missed the raw
dependency cycles; the return correctly rejected that check. The repaired packet
passes the landing tool's exact edge_fails check using every raw statement and
proof edge, with no tool-boundary exclusions. Each of the five new dependencies
has no path back to the basic-realization theorem after the correction.

Repair validation: the fresh server run compiled all six modules without warnings
(exit code 0; result aaf1fa31213e6cac88593301). No Lean file changed during the
repair. The landing checker reports zero added-edge cycle errors for the repaired
packet. Both changed-node statement histories pass check_statement_change.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
