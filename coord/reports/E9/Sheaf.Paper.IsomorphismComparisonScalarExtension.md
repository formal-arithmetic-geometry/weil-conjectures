## What changed

Filled the five original proofs without changing any public theorem statement or any
existing definition body.

The ordinary scalar models agree by uniqueness of the completed coefficient map and
their prescribed pure-tensor formulas. Universal left-derived-functor uniqueness gives
the derived model comparison; its counit normalization and the actual chain augmentation
identify its completion comparison with the specified scalarCompletion.

The sectionwise tensor isomorphism comes from uniqueness of left adjoints. The completed
coefficient transport square identifies the right adjoints, their units give the formula
on 1 tensor y, and linearity gives arbitrary transported coefficients. Sheafification and
tensor generation prove uniqueness.

Constructibility follows from preservation by completed pullback and the intrinsic
completion-adjunction normalization of the specified inverse-image comparison. The
completion unit is invertible on a constructible input, so this comparison is an
isomorphism and constructibility transports to inverse image.

For the final square, first prove the finite-level generator square. A generic additive
Roos calculation checks both actual cocone coordinates, including the zero shifted
coordinate, and gives the strict augmentation square. Its localization gives the ordinary
derived square on good representatives. Naturality and a good representative for every
derived object extend it to all objects. Naturality of the specified completion maps and
of the specified inverse-image comparison then proves the completed square by cancellation.
All technical helper statements are private and proved in the assigned module.

Validation: the complete proof route compiled through lcompile.py in 50.3 seconds
and passed the delivery compiler and axiom probe. After later runs exceeded the
60-second file limit, elaboration was simplified by retaining the original narrow
local-attribute scopes, using stricter type transparency throughout, and supplying
the ordinary model's coefficient maps and functors explicitly. The initial proof
block compiled in a profiled diagnostic file in 25.8 seconds; the tensor block also
compiled with stricter type transparency, in 27.9 seconds. The complete derived-
descent block compiled with that setting in 41.2 seconds. The final whole-file
compile and axiom probe are enforced by deliver3.py.

The additional proof-context commands and all 66 downstream consumers are recorded in
coord/changes/E9-isomorphism-scalar-comparison-proof-context.md. All existing public
signatures, definition bodies, visibility and public imports are preserved. No
consumer adaptation or target-meaning review is required.

## Proved and sorry left

Closed all five original holes:

- `WeilConjectures.isomorphismScalarSheafModel_existsUnique`.
- `WeilConjectures.isomorphismScalarModel_existsUnique`.
- `WeilConjectures.isomorphismScalarTensor_existsUnique`.
- `WeilConjectures.isomorphismComparisonInputs_constructible`.
- `WeilConjectures.isomorphismComparison_scalarExtension`.

Remaining holes in the delivered module: zero. Holes added: zero. Split-off statements:
zero. No definition or private helper contains a hole.

## No longer needed

Removed the original direct proof imports:

- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` (its declarations are
  reexported by retained dependencies; the good-representative argument still uses it).
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` (already reexported).
- `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`.
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`.

The following original direct proof dependencies are not used by the revised argument:

- `lem-weil-isomorphism-scalar-tensor-kflat-model`: the ordinary sectionwise tensor
  comparison is proved directly from the two adjunctions and then localized.
- `lem-weil-isomorphism-scalar-augmentation-cone`: the whole-cone square is proved here
  from the already stated finite scalar-pullback and augmentation formulas.
- `lem-weil-specified-pullback-comparison-alpha`: the actual scalarPullbackCompleted
  definition already conjugates scalarPullbackOrdinary by the specified completion maps.
- `lem-weil-isomorphism-derived-pullback-comparison-normalization`: the naturality and
  representative formulas of IsomorphismComparisonNatural suffice.

Removed obsolete top-level tool_uses approvals for
`lem-pur-isomorphism-inverse-image-tensor-hom`,
`lem-weil-isomorphism-derived-pullback-comparison-normalization`, and
`lem-pur-kflat-change-of-rings`. The retained approval is the scalar-operations comparison.
The flat-term K-flat resolution node remains needed to obtain good representatives.

Removed exploratory redundant direct imports of TensorColimitsIndependentCoefficients,
IntegralOperationsPreserveConstructible and SfIntegralConstructibleTriangulated: the
retained imports publicly reexport the declarations used. All original public imports
are retained. No module or declaration is withdrawn, and no source-library declaration
is removed or changed. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan imposed a separate K-flat tensor model and augmentation-cone
comparison that the actual ordinary scalar API makes unnecessary. The finite-level square
already follows from the tensor unit, the recorded pullback generator formula and
naturality. The additive Roos map is normalized on both coordinates, so the strict whole-
cocone calculation can be performed directly. The completed scalar-pullback comparison
is already defined by conjugation, so its stated definition supplies the final assembly.
The DAG proof, proof dependencies and proof origin now describe this route.

The coefficient-model clause needs no chosen finite-free basis: coefficient-map and
ordinary-functor witness uniqueness give its specified formula directly. For
constructibility, the intrinsic simultaneous realization calculus avoids converting to
the older finite-field completeness predicate.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
