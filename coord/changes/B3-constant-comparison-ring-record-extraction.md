# CategoryTheory.RingInverseImage

## Reason

Extract the existing operation-graph record into the module of the single-ring operation lemma,
so that the lemma can be imported by the item without an import cycle. Preserve its name,
universes, fields, visibility, and definition verbatim. The item publicly imports the new module
and retains all five original public imports. No consumer source change is required.

## Old

In `Sheaf.CategoryTheory.RouteInverseImageConstantComparison`:

```lean
structure RingInverseImage
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (R : Sheaf JC CommRingCat.{u})
    (RI : Sheaf JD CommRingCat.{u}) where
  ringUnderlying : L.obj ((sheafCompose JC (forget CommRingCat)).obj R) ≅
    (sheafCompose JD (forget CommRingCat)).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
          (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) +
          (@id (RI.obj.obj V)
            (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringMul : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
          (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) *
          (@id (RI.obj.obj V)
            (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringZero : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 0
  ringOne : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 1
```

## New

In `Sheaf.CategoryTheory.RouteInverseImageConstantRingOperations`, the identical declaration:

```lean
structure RingInverseImage
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (R : Sheaf JC CommRingCat.{u})
    (RI : Sheaf JD CommRingCat.{u}) where
  ringUnderlying : L.obj ((sheafCompose JC (forget CommRingCat)).obj R) ≅
    (sheafCompose JD (forget CommRingCat)).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
          (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) +
          (@id (RI.obj.obj V)
            (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringMul : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
          (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) *
          (@id (RI.obj.obj V)
            (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringZero : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 0
  ringOne : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 1
```

The original module additionally has
`public import Sheaf.CategoryTheory.RouteInverseImageConstantRingOperations`.
Its theorem signature is unchanged. The declaration's DAG attachment moves from the parent node's
`lean.declarations` to `lem-route-inverse-image-constant-ring-operations`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RouteInverseImageConstantComparison | B3 | Publicly imports the extracted record; original theorem signature unchanged. |
| Sheaf.CategoryTheory.GeometricRingInverseImage | unclaimed in shared snapshot | Sole original direct importer and external user; no signature or source adaptation. Compile against extracted record required. |

The four new helper modules are part of this delivery. No existing source-library module changes.

## Status

landed 20261028T055609-L-772760 2026-10-28 (merge of deliver/B3/Sheaf.CategoryTheory.RouteInverseImageConstantComparison)
