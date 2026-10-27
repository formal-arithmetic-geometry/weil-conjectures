## What changed

Completed existing proof obligations in
`Sheaf.Paper.SfCbcExtensionZeroCompletion`. Existing public signatures,
definition bodies and public imports are preserved.

The constant coefficient maps on the slice and AsSmall model are constructed
from continuous-pushforward/sheafification compatibility. Their stated unit
formulas follow from compatibility with sheafification's unit, which also
proves uniqueness. The slice module transport and small-model module transport
are additive equivalences; exact localized extension then proves
`sfCbcOpenExtension_exact`.

For `sfCbcFiniteCompletedHom_inverse`, transport the chosen completion model's
realization along the unit-preserving Roos comparison, keeping its complex.
The quotient augmentation is unchanged by its uniqueness property. The
reduction Hom equivalence identifies the projection adjoint with the existing
`adicCompletionReduction_isIso`. Unit naturality and the completion projection
identity identify its composite with the reduced unit as identity. Compose
with `sfCbcFiniteTensorHom` and cancel to obtain the specified inverse formula.
This uses the existing, still unfinished tensor and Roos comparison obligations.

Added only proved private helpers and the private proof import
`Mathlib.CategoryTheory.Sites.Equivalence`. Local irreducibility of the model
transport definitions prevents repeated expansion during elaboration. Updated
the existing node's transport and finite-inverse proof descriptions. No new
public declaration, definition repair or consumer adaptation is introduced.

## Proved and sorry left

Closed 5 of the 18 existing holes:

- `AlgebraicGeometry.Scheme.sfCbcConstantSliceMap_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcOpenExtension_exact`
- `AlgebraicGeometry.Scheme.sfCbcModelRingMap_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcModelModules_properties`
- `AlgebraicGeometry.Scheme.sfCbcFiniteCompletedHom_inverse`

Added 0 holes and split off 0 statements. All 13 remaining holes are
unchanged public theorems belonging to
`lem-sf-cbc-extension-zero-completion`:

- `AlgebraicGeometry.Scheme.sfCbcExtensionModel_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcOrdinaryTensorComparison_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcTensorComparison_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcReducedCompletionUnit_isIso`
- `AlgebraicGeometry.Scheme.sfCbcRestrictExtensionIso_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcFiniteTensorHom_isIso`
- `AlgebraicGeometry.Scheme.sfCbcCompletionModelIso_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcFiniteUnderlyingHom_transition`
- `AlgebraicGeometry.Scheme.sfCbcFiniteCompletedHom_naturality`
- `AlgebraicGeometry.Scheme.sfCbcModelComplex_kflat`
- `AlgebraicGeometry.Scheme.sfCbcFiniteModelIso_existsUnique`
- `AlgebraicGeometry.Scheme.sfCbcCompletedReductionIso_evaluation`
- `AlgebraicGeometry.Scheme.sfCbcRealizationExtensionIso_existsUnique`

These proofs use existing statements that may themselves depend on sorry;
they do not assert that the full transitive axiom closure is already sorry-free.

## No longer needed

No import, module or node is withdrawn. The remaining comparison obligations
retain their declared dependencies, and the original proof imports supply
instance context for published definitions. No blueprint unit is bypassed.
The four transport proofs use sheafification compatibility and the actual
ringed-site equivalences directly; no additional transport obligation is added.

## Where the brief, the DAG or earlier work was wrong

No false statement or altered mathematical route was found. The existing
completion-reduction theorem applies after transporting the completion model's
realization; the needed quotient augmentation equality follows from its existing
unique section formula. This avoids a new finite-inverse auxiliary obligation.

Edge cases checked against the statements: identity and empty open immersions,
the zero coefficient ring and zero complex, and arbitrary noncomplete input.
The transport proofs use only site equivalences and unit formulas. The finite
inverse proof retains the actual quotient coefficients and needs no completeness
hypothesis on the original input.

The compilation checks use the prescribed remote `lcompile.py`. Profiling is
removed from the delivered file; the time limit is unchanged.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
