## What changed

Proved `AlgebraicGeometry.Proj.scalarExtension_twistMap_basicOpen_bijective` by reducing to the complete-chart theorem on the image standard-open basis and applying the module-sheaf basis isomorphism criterion. Added the proof-only import of `WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis` and a new split-off module stating the image standard-open basis lemma.

## Proved and sorry left

Closed the `scalarExtension_twistMap_basicOpen_bijective` sorry. Added one strictly lower sorry, `AlgebraicGeometry.Proj.scalarExtension_image_basicOpen_isBasis`, in `Sheaf.AlgebraicGeometry.ProjScalarExtensionImageBasicOpenBasis`; it is the geometric basis-refinement step used by the proof.

## No longer needed

The parent proof uses only `lem-sfb-proj-scalar-extension-twist-chart-basic` and the new image-basis node. The previously listed localization, affine-section, tilde, and graded-module-sheaf nodes are not imported or used directly by this proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan listed the full localization and affine tilde calculation even though the complete-chart theorem already packages that calculation. The remaining arbitrary-open step is a basis argument; the DAG had no declaration for the image-standard-open basis, so it is split off as a new node.

## New nodes

`lem-sfb-proj-scalar-extension-image-basic-open-basis`: image standard opens form a basis of `Proj ℬ` under the graded spanning and irrelevant-ideal hypotheses. Its Lean declaration is in `lean/Sheaf/AlgebraicGeometry/ProjScalarExtensionImageBasicOpenBasis.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjScalarExtensionImageBasicOpenBasis": "47938cf494ea98933d5860c60490ba129f1e48b7", "Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistChart": "49bd5b890aa5f3ce38326408c81d087c8fc99c3f"}, "results": {}, "time": "2026-10-28T08:05:48+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
