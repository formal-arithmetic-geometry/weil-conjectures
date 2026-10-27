## What changed

Proved three existing theorems in `Sheaf.Paper.SfCbcExtensionZeroCompletion`,
without changing any declaration type or definition.

- `sfCbcTowerExtension_exact`: additivity of postcomposition and pointwise
  preservation of finite limits and colimits.
- `sfCbcEtaleExtension_boundedBelow`: retain the input lower bound using the
  existing exact-functor lemma `Functor.isGE_mapDerivedCategory_obj`.
- `sfCbcExtensionZeroCompletion`: combine the existing reduced-unit and finite
  inverse theorems, cancel the natural isomorphism, transport completeness from
  `ConstantCompletion.koszul_quotient_reflector` through the small-model counit,
  and construct the witness using `sfCbcTransportEtaleWitnessIso`.

Added the proved private helper `sfCbcComplete_of_iso`, expressing invariance of
local derived completeness under isomorphism. Its proof applies slice restriction
and derived internal Hom to the isomorphism and transports each IsZero assertion.
It introduces no new assumption or public API.

The final theorem's unused retained-witness binder is preserved verbatim; its
unused-variable linter is disabled only for that declaration. Private proof
imports were retained when their removal regressed compilation time. Updated
the existing node's completion-reflector step.

## Proved and sorry left

Closed 3 of the original 21 holes:

- `AlgebraicGeometry.Scheme.sfCbcTowerExtension_exact`
- `AlgebraicGeometry.Scheme.sfCbcEtaleExtension_boundedBelow`
- `AlgebraicGeometry.Scheme.sfCbcExtensionZeroCompletion`

Added 0 holes and split off 0 statements. These proofs use existing named
statements that still contain sorry; this does not assert that their transitive
axioms are already free of sorryAx. The remaining 18 holes are all unchanged
public theorems attached to `lem-sf-cbc-extension-zero-completion`:

- `AlgebraicGeometry.Scheme.sfCbcConstantSliceMap_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcOpenExtension_exact`
- `AlgebraicGeometry.Scheme.sfCbcModelRingMap_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcModelModules_properties`
- `AlgebraicGeometry.Scheme.sfCbcExtensionModel_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcOrdinaryTensorComparison_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcTensorComparison_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcReducedCompletionUnit_isIso`
- `AlgebraicGeometry.Scheme.sfCbcRestrictExtensionIso_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcFiniteTensorHom_isIso`
- `AlgebraicGeometry.Scheme.sfCbcCompletionModelIso_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcFiniteCompletedHom_inverse`
- `AlgebraicGeometry.Scheme.sfCbcFiniteUnderlyingHom_transition`
- `AlgebraicGeometry.Scheme.sfCbcFiniteCompletedHom_naturality`
- `AlgebraicGeometry.Scheme.sfCbcModelComplex_kflat`
- `AlgebraicGeometry.Scheme.sfCbcFiniteModelIso_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcCompletedReductionIso_evaluation`
- `AlgebraicGeometry.Scheme.sfCbcRealizationExtensionIso_existsUnique`

## No longer needed

No import or module is withdrawn. The existing proof imports also supply
instance context for this file's published definitions. Removing them caused a
60-second timeout, so they are retained in this partial delivery.

The final completeness argument uses the existing constant quotient-completion
reflector directly, so `lem-sp-completed-pullback-adjunction` is removed from
this node's proof dependencies. It remains a statement dependency and is not
withdrawn. Other declared dependencies are retained for the unchanged
specialized comparison obligations. No module or DAG node is deleted, and no
blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The generic quotient-completion reflector already
contains the required completeness conclusion. Transport across the counit of
the small-model derived equivalence suffices; a separate completed-pullback
adjunction construction is unnecessary for this clause.

Local irreducibility of the large transport/comparison terms and quotient
presentation keeps their bodies out of subsequent elaboration while preserving
every public definition and signature. No definition was changed and no time
limit was raised. The delivered module compiled without warnings through
`lcompile.py` in 49.8 seconds. Delivery preflight performs the independent packet
checks.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
