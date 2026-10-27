## What changed

Completed `cbcModulePullbackAdjunction_exists`,
`cbcDerivedInverseExchange_exists` and `cbcDerivedInverseExchange_isIso` in
`lean/Sheaf/Paper/CompletedExtensionZeroComparison.lean`.
The exact completed-module pullback presentation already proved in
`CompletedTowerPullback` supplies universal-counit normalized comparisons.
Proved private generic lemmas derive the exchange using
`Functor.mapDerivedCategorySquareIso`, verify precisely the existing
normalization equation, and prove invertibility from it. Cancellation
against invertible target counits and K-flat representatives proves uniqueness; the same normalization and
naturality prove invertibility on every derived object. The module-pullback
adjunction composes the existing small-model inverse-image adjunction with
scalar extension, transports its right adjoint sectionwise, verifies the
sheafified pure-tensor unit, and proves uniqueness by equality of units.

The proof imports the existing private exact-presentation API through
`import all Sheaf.Paper.CompletedTowerPullback`, and privately imports
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
The proof also imports the proved private inverse-image adjunction through
`import all Sheaf.AlgebraicGeometry.ProEtaleOperations`.
The existing node records the adjunction and ordinary-derived subarguments
and their K-flat resolution dependency. All existing public signatures, attributes, public
imports and definition bodies are preserved. No other existing Lean module
is changed.

## Proved and sorry left

Closed three of the seven original holes:

- `AlgebraicGeometry.Scheme.cbcModulePullbackAdjunction_exists`.
- `AlgebraicGeometry.Scheme.cbcDerivedInverseExchange_exists`.
- `AlgebraicGeometry.Scheme.cbcDerivedInverseExchange_isIso`.

No holes added and no statements split off. Four original holes remain,
all under `lem-cbc-completed-extension-zero-comparison`:

- `AlgebraicGeometry.Scheme.cbcOpenAdjunction_exists`.
- `AlgebraicGeometry.Scheme.cbcRightExchange_exists`.
- `AlgebraicGeometry.Scheme.cbcCompletedExchange_exists`.
- `AlgebraicGeometry.Scheme.completedExtensionZeroComparison`.

The derived-exchange proofs use the already declared underived exchange;
its section-normalized right exchange and the open adjunction remain
independent obligations. The completed-limit and completeness assembly is unchanged.

Validation: `lcompile.py` compiled the final module cleanly in 50.7 seconds
(exit code 0), within the 60-second limit. Delivery preflight is performed
by `deliver3.py`.

## No longer needed

No module is withdrawn, and no node is globally pruned. No existing import
is removed. The derived-exchange subargument does not need a separate
extension-preserves-K-flat proof: exactness of the recorded pullback makes
the target counit invertible on every representative. The original
flat-resolution, strict-reduction, product, Koszul and strict finite
exchange nodes remain necessary for the unfinished completed assembly;
their dependencies and unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier docstring plan for derived exchange proposed proving preservation
of K-flat representatives by extension by zero. The current library already
proves that the recorded completed module pullback is exact, so universal
left-derived uniqueness supplies an invertible target counit without that
extra preservation argument. The construction still satisfies exactly the
original K-flat normalization, with no statement or coefficient change.

The umbrella node's current Lean attachment names
`Sheaf.Paper.CompletedOpenExchangeTransport`; this item retains its
blueprint-tagged supporting declarations. Its existing attachment is
preserved, and only its proof route is supplemented.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
