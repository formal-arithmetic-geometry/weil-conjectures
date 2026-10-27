## What changed

Prove `SheafOfModules.ringedTensor_adjunction_mate` with its existing statement.
Construct the inverse-image tensor comparison, compose it with the normalized
scalar-extension comparison, identify every normalized comparison with the specified
adjunction mate, and compute the tensor and unit inverse formulas.

The inverse-image comparison uses the proved, independently sized
`CochainInversePairing.exists_inverseImageTensorComparison` from
`Sheaf.SecSmoothPurity.CochainInverseComparison`. Its pure-section API supplies
restriction, tensor naturality and tensor generation. The scalar factor transports
`scalarTensorBinaryIso` through `tensorObjIsoSheafification` and `siteTensorRightIso`;
the proved generator formulas give both scalar formulas. The unit comparison reuses the constructed
`inverseImage_unit_iso` in
`StrictPerfectRingedPullbackModel`. The scalar unit formula comes from
`ScalarExtensionBinaryCoherence`. Every imported result used here is already
proved. All new helpers are private and proved.

The node follows this argument. The local scalar comparison is kept behind its
section API; the final tensor formulas use direct equality calculations instead
of broad rewrites. The standard syntax-linter set
is disabled locally to avoid repeated traversal of the large fixed statement.
Kernel checking and the full
delivery axiom audit remain enabled.

## Proved and sorry left

Proved (the full proof and official axiom audit compiled in 53.9 seconds on the server):
`SheafOfModules.ringedTensor_adjunction_mate`, the item's one hole at
`lem-pd-ringed-tensor-adjunction-mate`.
No holes added; no private or definition holes; no new public declarations.
All diagnostic modules were removed from the packet before delivery.

## No longer needed

The revised proof does not use these planned dependencies:

- `lem-weil-pbc-algebraic-inverse-image-tensor-comparison`, module
  `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`: its public theorem has
  narrower universes; use the independently sized theorem already proved in `CochainInverseComparison`.
- `lem-weil-pbc-scalar-extension-tensor-comparison`, module
  `Sheaf.Paper.RingedTopoiScalarTensorComparison`: use the independently sized
  explicit scalar comparison already proved in `ScalarExtensionBinaryCoherence`.
- `lem-pd-generalized-tensor-normalization-unit-equation`, module
  `Sheaf.Paper.GeneralizedTensorNormalizationUnitEquation`: prove the required
  unit equation directly by testing the product of the two underlying sheaves.
- `lem-pd-sheaf-scalar-tensor-inverse-formulas`, module
  `Sheaf.Paper.SheafScalarTensorInverseFormulas`: compute the forward and inverse
  scalar formulas by linearity of the normalized independent scalar isomorphism.
- `lem-pc-sites-sheaf-tensor-bilinear-universal`, module
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`:
  use the independent tensor-generation API already proved in `CochainInverseComparison`.
- `lem-pc-sites-module-sheafification-bilinear-extension`, module
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`:
  the existing independent inverse-image comparison supplies this descent.

The corresponding obsolete `tool_uses` approvals for the first two and last two
nodes are removed. No source-library declarations or modules are withdrawn.
The geometric-construction, transport, bilinear descent and pairing arguments
are reused: the existing independent inverse-image comparison contains them.
No new direct imports of `GeometricModuleConstruction`, `GeometricModuleTransport`,
`RingedToposKFlatPullback` or `CochainTensorCoherenceData` are needed.
The private mate and naturality helpers work in arbitrary monoidal categories;
all module-specific constructions remain behind their proved APIs.
The original module's six
public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The stated inverse-image and scalar-comparison dependencies do not apply directly
to the item's independent universe parameters. The library already provides
the required independent-universe inverse-image comparison in another module.
The generalized-normalization split uses a different algebraic inverse-image
interface; the item proves its required equation directly for the supplied interface.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
