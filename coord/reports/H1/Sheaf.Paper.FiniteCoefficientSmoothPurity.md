## What changed

Filled `WeilConjectures.PurityFiniteSetting.isIso_smoothPurityMap` in
`Sheaf.Paper.FiniteCoefficientSmoothPurity` using the current blueprint's three-factor
argument. The public theorem signature, public imports and all existing definitions
are unchanged. Three proved private helpers transfer a Tor interval along an
isomorphism, produce a bounded etale finite-Tor presentation of the original intrinsic
object, and show invertibility of the specified tensor mate in that presentation.

The proof uses the existing finite-ring constructible-derived-origin theorem and
intrinsic Tor transport, then the tensor clause of cohomological smoothness. It tensors
the inverse of the recorded normalized diagonal orientation, uses the unique-morphism
specification of the intrinsic tensor map, and composes with the canonical reassociation.
There is no substitution of an arbitrary isomorphism between the endpoints.

Updated the existing node's proof, proof dependencies and proof origin to this argument.
No other module is edited. Added proof-only imports of
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport` and
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
All compilation uses the required lcompile.py server tool.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.isIso_smoothPurityMap`
(node `thm-pur-finite-coefficient-smooth-purity`). Added zero holes. No `sorry` remains
in the delivered module. The proof uses existing stated dependencies, including
cohomological smoothness and the normalized diagonal orientation, whose own proofs
remain separate tasks. This is one proof from existing declarations, not a decomposition.

The proof preserves the original K, its finite-Tor constructibility hypothesis, every
positive coefficient level, and d = 0. Empty schemes and K = 0 cause no exception: finite
cohomological support supplies bounds even for an empty support. The construction uses
finite commutative quotient rings and does not assume the coefficient ring is a field.

## No longer needed

Removed the following proof-only direct imports:

- `Sheaf.Targets.VectorBundlePurity`
- `Sheaf.AlgebraicGeometry.VectorBundleIntegration`
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.DualizingObjectPurity`
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
- `Sheaf.Paper.PurityDiagonalDualizingObject`
- `Sheaf.Paper.VectorBundlePurity`

The diagonal orientation and Noetherianity APIs remain available through the statement
imports. Removing their redundant direct imports does not prune their mathematics.
The four existing public imports retain the file's existing exported interface.

Removed direct proof dependencies `lem-pur-vector-integration-chart-comparison`
(`Sheaf.Paper.VectorIntegrationChartComparison`) and `lem-pur-vector-model-chart-descent`
(`Sheaf.Paper.VectorModelChartDescent`): the current blueprint proof consists precisely
of the three specified isomorphism factors, with no separate vector-model agreement
conclusion. The current unit statement in literature/blueprint/latest likewise states
canonical finite-coefficient purity without the old extra model-agreement clause.
These modules and nodes are not withdrawn: other parents may still need them.

Pruned obsolete approved tool uses `thm-amb-vector-bundle-purity` and
`lem-pur-twist-sheaf-locally-free`. Kept `lem-weil-pbc-finite-type-over-noetherian`,
which supplies the compactification domain used by the proof.

The old separate dependency `def-weil-exceptional-inverse-image` is represented through
`def-pur-smooth-purity-map`'s actual exceptional-functor construction; it is not a separate
lemma of this proof. No claim of whole-library unreachability is made for any module.

## Where the brief, the DAG or earlier work was wrong

The old Lean docstring and stored DAG proof contained an extra vector-bundle
model-agreement branch. The current main-20261025 blueprint proof explicitly uses only
reassociation, the diagonal orientation and the orientation-free tensor formula.
The sandbox proof and documentation follow that current source. Its diagonal/DNC route
is retained through `diagonalDualizingObject`; no unit route is replaced.

The original DAG omitted the actual intrinsic-to-fixed-coefficient presentation glue.
Existing nodes `lem-weil-pbc-finite-ring-constructible-derived-origin` and
`lem-exc-intrinsic-tor-amplitude-transport` supply it, so no new statement is needed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
