# WeilConjectures.CompactSupportFiniteProjection.iterationTensorComparison

## Reason

After the unary cancellation is proved, tensoring it still triggers a long kernel
conversion through the concrete coefficient equivalence unit. Factor the original
inverse unit followed by the tensor comparison through `unitTensorRealization`.
This generic construction has explicitly stated endpoints and the original two
factors as its body. It constructs the same isomorphism.

The binders, visibility, inferred result type up to definitional equality, and
specified map are unchanged. Add a public import of its defining module. The
iteration module is unclaimed in the current shared claim records. Add the proved
private helper `map_unit_tensor_trans`, unfolding the generic construction before
specialization, and use it for `hsplit` in the existing iteration proof. No public
theorem signature changes.

## Old

```lean
def iterationTensorComparison :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let Pf := fixedDerivedPull (C := C) (E := E) (n := n) f
  (RX.unitIso.app
    (((TX.obj (RX.inverse.obj K.obj)).obj
      (RX.inverse.obj ((torPull S f).obj ((torPull S g).obj L)).obj)))).symm ≪≫
    (TX.obj (RX.inverse.obj K.obj)).mapIso
      (fixedPullRealization S f
        ⟨((torPull S g).obj L).obj, ((torPull S g).obj L).property.1⟩ ≪≫
        Pf.mapIso (fixedPullRealization S g ⟨L.obj, L.property.1⟩))

```

## New

```lean
def iterationTensorComparison :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let Pf := fixedDerivedPull (C := C) (E := E) (n := n) f
  unitTensorRealization RX TX (RX.inverse.obj K.obj)
    (fixedPullRealization S f
        ⟨((torPull S g).obj L).obj, ((torPull S g).obj L).property.1⟩ ≪≫
        Pf.mapIso (fixedPullRealization S g ⟨L.obj, L.property.1⟩))

```

## Users

These are all declaration users from `tools/downstream.py --uses`, with the new
item consumer. The existing direct importer is the item's module; its new data
and endpoint helper modules also import the iteration comparison.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.FiniteProjectionIterationRealization` | unclaimed | Use a proved generic helper in the existing iteration proof. |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | T3 | Apply tensor transport with the generic unit-and-tensor constructor. |
| `Sheaf.Paper.FiniteProjectionCompositionData` | T3 | Retain the original iteration target comparisons and their published formulas. |
| `Sheaf.Paper.FiniteProjectionCompositionEndpointProofs` | T3 | Prove tensor transport using the generic constructor. |

## Status

landed 20261028T055804-L-809833 2026-10-28 (merge of deliver/T3/Sheaf.Paper.FiniteProjectionCompositionRealization)
