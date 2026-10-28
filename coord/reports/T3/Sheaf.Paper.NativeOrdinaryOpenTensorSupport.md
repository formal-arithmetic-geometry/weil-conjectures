## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_open_tensor_support`
without changing its public signature or any other module. Added only proof imports
and five proved private helpers in the item module. Updated its proof docstring and
DAG route to match the Lean proof.

The fixed ordinary tensor is identified with the canonical derived module tensor
by `nativeOrdinary_tensorRight_iso`. Open/complement pullback detection proves
sheaf tensor support. Coproduct closure proves support of every total-complex term;
the termwise counit and its localization exhibit an extended derived object.
The canonical K-flat tensorator computes the unbounded derived tensor. Finally,
localization of the invertible ordinary open unit gives full faithfulness, and the
specified exact derived adjunction's counit is invertible on this essential image.

The complete proof compiled through lcompile.py in 35.2 seconds before final lint
cleanup. Delivery performs the final compile and axiom check. The argument applies
to zero inputs and the empty open; no boundedness, constructibility, Weil lift,
projection comparison, or forgetting compatibility is assumed for M or N.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_open_tensor_support`
(node `lem-sf-native-ordinary-open-tensor-support`).

Five private support helpers are proved. No `sorry` remains in the delivered Lean
file; no hole is added or split off. Existing dependencies retain their existing
proof status; this is a proof from library declarations, not a claim that all
transitive dependencies are axiom-free.

## No longer needed

The planned dependency `lem-sf-open-tensor-support`
(`Sheaf.SixFunctors.OpenTensorSupport`) is not needed by this proof. Its
`Operations` uses sectionwise ring-module categories, whereas the actual ordinary
adic category uses module objects in sheaves of coefficient modules. The canonical
module-object tensor and the proved source-library open/complement detection give
a direct route without constructing unrelated ringed base-change operations.
Its auxiliary `Sheaf.SixFunctors.OpenTensorSupportAux` is consequently not imported
for this route either. Neither module is withdrawn; other parents may use them.

No existing import was removed: the original public import of
`Sheaf.Paper.NativeOpenTensorOperations` is retained. No module is deleted.
The fixed ordinary tensor model's full normalized total-tensor witness is not
needed here; its ordinary Hom model already identifies the tensor by adjoint
uniqueness. The exact derived adjunction and native closed comparison remain used.

## Where the brief, the DAG or earlier work was wrong

The conclusion is unchanged and no statement was found false. The old DAG's
instruction to apply the generic sectionwise support theorem directly omitted a
comparison between different module-category presentations. The proof avoids that
comparison entirely, using the established native ordinary tensor identification
and source-library support detection. The source proof on module-object derived
categories already supplies the K-flat/totalization pattern, which is adapted to
the actual ordinary adic coefficient module here. The unit route is unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryOpenTensorSupport": "50286b666d96dee6180a54c71259b759878cec21"}, "results": {"Sheaf.Paper.NativeOpenTensorForgetNormalization": {"hash": "3fd4b9f7f6f6ee071fdf4e542482e3632ec028a7", "status": "OK"}}, "seconds": 107, "time": "2026-10-28T14:10:13+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
