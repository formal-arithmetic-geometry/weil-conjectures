## What changed

Replaced the proof hole of `WeilConjectures.integralPullbackCounitProjection`
without changing its signature. The proof chooses the existing coherent primitive
reduction presentation, applies the realization normalization, computes the Roos
projections on K-injective towers and extends by naturality, applies the evaluated
counit formula under the finite adjunction, and transports the result along the
arbitrary representative isomorphism `e`.

Added `Sheaf.Paper.IntegralPullbackStrictFiniteComponent`. Its canonical
`integralComparisonRestrictedEvaluationFactors` is an explicit composite of the
existing exact-functor isomorphisms. Its theorem isolates the finite component of
a strict comparison fixed on inverse-image unit generators. It has no calculus,
integral realization, counit, representative isomorphism, constructibility or
good-complex hypothesis. Both sides retain the exact-restriction factor between
the localized restricted tower term and restriction of the localized finite term.

Updated the item's proof route and added a node for the strict finite component.
All existing public imports and all existing declaration signatures are preserved.
No adopted source-library file is changed.

## Proved and sorry left

The item's original hole is replaced by a complete proof from the existing
statements and `WeilConjectures.integralPullbackStrictFiniteComponent`.
The private helpers `roos_projection_natural`, `normalized_roos_projection`,
`bridge_projection`, and `evaluated_counit_adjunct` have complete proofs.

One new hole remains: `WeilConjectures.integralPullbackStrictFiniteComponent`,
node `lem-pod-integral-pullback-strict-finite-component`. Its entire proof is
`:= by sorry`. There are no other holes added, and no hole in any definition.
This is a decomposition: one upper hole closed, one strictly smaller lower hole
added, net zero holes closed. It does not claim an unconditional proof of the
original statement.

The finite component is a genuine part of the argument: it compares an arbitrary
strict tower isomorphism satisfying a generator equation with ordinary finite
inverse image. The parent separately proves the limit/projection normalization,
uses the realization's whole-tower equation, identifies the specified counit,
and transports from the representative. None of those tasks is in the lower
statement.

## No longer needed

The direct proof dependency `lem-weil-strict-roos-comparison`
(`Sheaf.CategoryTheory.StrictRoosComparison`) is not used. Instead, the prescribed
`IntegralComparisonRoosModel.computes` equation and the existing ordinary-limit
projection normalization prove the precise projection equation required here,
with a naturality argument on a K-injective resolution.

No public import was removed, and no module was withdrawn. The remaining original
dependencies are retained where their definitions, finite models or projection
construction are used. The coherent primitive presentation is an existing proved
result; its construction is not duplicated.

## Where the brief, the DAG or earlier work was wrong

The old proof text proposed taking an arbitrary presentation from
`S.reductionModel` and applying `M.normalization`. The current normalization also
requires whole-system presentation coherence; the finite presentation equations
alone do not give that hypothesis. The existing theorem
`coherentPrimitiveReductionPresentation` supplies both conditions, and this proof
uses it. No faithfulness of finite derived evaluation is asserted. The node
`lem-trf-coherent-primitive-reduction-presentation` is used as a tool from
`sk-thm-trace-transport`: it supplies precisely the whole-system coherence absent
from the original reductionModel interface. It does not replace any step of the
item's unit; it supplies the presentation needed to perform its stated step 1.
No maintainer `tool_uses` approval field has been added or rewritten.

The exact-restriction factorization cannot be suppressed between `Q(Res C_n)`
and `Res(Q C_n)`. It is explicit in the finite-component theorem and in the
assembly, matching the definition of `integralPullbackFiniteComparison`.

The blueprint ancestry command could not traverse the existing item's ancestry
(`blueprint.from.node = None`). The new node records the existing chain through
`lem-pod-integral-pullback-system-comparison` and
`lem-pod-integral-pullback-composition` to `def-weil-local-frobenius-trace`, read
from their records. The unit's realized route is unchanged.

## New nodes

`lem-pod-integral-pullback-strict-finite-component`, in
`dag/nodes/sec-poincare-duality/`, states the finite strict-component calculation
from step 1 of the original proof. Its docstring and node give the argument using
local surjectivity of the completed coefficient projection, the ordinary finite
inverse-image adjunction, the two unit-normalized presentation comparisons, and
exact localization. The statement includes arbitrary complexes and the cases
`n = 0`, zero complexes, and empty schemes. It does not assume a finite derived
counit is invertible. The explicit factorization definition chooses no new data
from an unproved existence theorem. No change record is needed: the delivery
changes no existing public signature, definition, instance or public import.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
