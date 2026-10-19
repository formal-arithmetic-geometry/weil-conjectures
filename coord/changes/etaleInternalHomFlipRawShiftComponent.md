# etaleInternalHomFlipRawShiftComponent

## Reason

The original `simpa` body left a dependent cast opaque at the component
boundary.  The naturality proof needs the cast represented explicitly by the
canonical `eqToIso` for `neg_neg n`; this is definitionally the same composite
map and exposes the equality needed by the generic opposite-shift lemma.

## Old

```lean
by
  simpa only [neg_neg, op_unop, Functor.comp_obj, Functor.flip_obj_obj] using
    (((RHom(X)[B]).flip.obj M).mapIso
      ((shiftFunctorOpIso _ n (-n) (add_neg_cancel n)).app K) ≪≫
        (etaleInternalHomSourceShiftIso B K.unop (-n)).app M)
```

## New

```lean
(((RHom(X)[B]).flip.obj M).mapIso
  ((shiftFunctorOpIso _ n (-n) (add_neg_cancel n)).app K) ≪≫
    (etaleInternalHomSourceShiftIso B K.unop (-n)).app M) ≪≫
  eqToIso (congrArg (fun a ↦ (((RHom(X)[B]).obj K).obj M)⟦a⟧) (neg_neg n))
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctors.EtaleGenericHomTriangle` | Q1 | Uses the explicit equality transport in the naturality proof. |

## Status

landed 20261019T231307-L-570465 2026-10-19 (merge of deliver/Q1/Sheaf.SixFunctors.EtaleGenericHomTriangle)
