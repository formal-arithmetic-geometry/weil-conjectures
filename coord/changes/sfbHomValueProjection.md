# WeilConjectures.SfbHomFilteredColimit.homValue

## Reason

Evaluate the canonical Hom-product projection through `homComplexπ` directly.
The previous definition used `coefficientHomComponent`, whose implementation has
already been changed to this same projection in
`coord/changes/coefficientHomComponentProjectionAPI.md`. The last green compiled
artifact still expands the older nested choice representation. Converting this
representation repeatedly during local-section calculations spends substantial
kernel time: the complete proof compiled in 49.1 seconds before this change and
37.0 seconds afterwards. The original private projection-equality lemma proved
this equality by `rfl`; it is no longer needed.

The signature and value of `homValue` are unchanged. This is the same projection,
not a new choice of evaluation. The private component and differential proofs now
use the projection API throughout. `HomComplexComponents` becomes a public import
because the definition uses its projection directly. No source-library module is
changed, and no target signature is changed. Any target meaning that depends on
this definition is submitted for the semantic review required by AGENTS.md §4;
the equality of evaluations is the justification that its meaning is preserved.

## Old

```lean
noncomputable def homValue (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n p q : ℤ) (h : p + n = q)
    (U : Cᵒᵖ) (f : ((homComplex (R := R) P Q).X n).val.obj U)
    (x : (P.X p).val.obj U) : (Q.X q).val.obj U :=
  (((coefficientHomComponent.{r, u, v} J R P Q n p q h).val.app U f).app
    (op (Over.mk (𝟙 U.unop)))).hom x
```

## New

```lean
noncomputable def homValue (R : Sheaf J CommRingCat.{max u v r})
    (P Q : CochainComplex (Modules.{u, v, r} J R) ℤ) (n p q : ℤ) (h : p + n = q)
    (U : Cᵒᵖ) (f : ((homComplex (R := R) P Q).X n).val.obj U)
    (x : (P.X p).val.obj U) : (Q.X q).val.obj U :=
  (((homComplexπ.{u, v, max u v r, max u v r} (J := J) (R := R) P Q n p q h).val.app U f).app
    (op (Over.mk (𝟙 U.unop)))).hom x
```

## Users

`python3 tools/downstream.py Sheaf.Paper.DerivedInternalHomFilteredColimit
--uses homValue` reports zero downstream modules and only the defining module as
a declaration user. A separate text search confirms that the similarly named
`homValue` in `Sheaf.Paper.PointDerivedHomEvaluation` belongs to another namespace.
All existing public signatures in the item remain verbatim; the complete item
compiles against the changed definition. No consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | R4 | Same evaluation; private proofs use the projection API. |

## Status

landed 20261020T221331-L-4175439 2026-10-20 (merge of deliver/R4/Sheaf.Paper.DerivedInternalHomFilteredColimit)
