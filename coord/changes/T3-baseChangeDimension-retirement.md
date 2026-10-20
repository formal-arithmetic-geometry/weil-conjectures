# AlgebraicGeometry.baseChange_dim

## Reason

Retire the unused Sheaf duplicate assigned in coord/retire-items.tsv. The actual
source replacement is WeilConjectures.AlgebraicGeometry.BaseChangeDimensionExtension,
not the similarly named WeilConjectures.AlgebraicGeometry.BaseChangeDimension.
The two files are byte-for-byte identical from `module` onward. The public theorem
and its complete proof therefore already exist in the adopted source library.

## Old

Module: Sheaf.AlgebraicGeometry.BaseChangeDimension.

```lean
theorem baseChange_dim {k k' : Type u} {C : Scheme.{u}} [Field k] [Field k']
    [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    (f : C ⟶ Spec (.of k)) [IsCurve f] :
    topologicalKrullDim (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}) =
      topologicalKrullDim C
```

## New

Module: WeilConjectures.AlgebraicGeometry.BaseChangeDimensionExtension.
The same declaration, signature, and proof are retained there verbatim. The Sheaf
copy is withdrawn using deleted.txt, and node base-change-dimension is reattached
to the existing source declaration. No definition or statement changes meaning.

```lean
theorem baseChange_dim {k k' : Type u} {C : Scheme.{u}} [Field k] [Field k']
    [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    (f : C ⟶ Spec (.of k)) [IsCurve f] :
    topologicalKrullDim (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}) =
      topologicalKrullDim C
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BaseChangeDimension | T3 | Withdraw unused duplicate. |
| WeilConjectures.AlgebraicGeometry.BaseChangeCurve | unmodified | Already imports the source replacement and applies baseChange_dim in baseChange_curve. |

`tools/downstream.py Sheaf.AlgebraicGeometry.BaseChangeDimension --uses
AlgebraicGeometry.baseChange_dim` reports zero downstream modules. A full Lean
source import search likewise finds no importer of the withdrawn module.
The old retirement inventory's Sheaf.AlgebraicGeometry.BaseChangeCurve consumer
has already moved to the source tree. No consumer adaptation is necessary.
No source-library file is changed; all adopted declarations and imports remain.
No target signature or underlying definition changes.

Validation: a remote single-file probe imported both source modules and proved
exactly the former Sheaf theorem's signature by `exact baseChange_dim f`.
`#print axioms AlgebraicGeometry.baseChange_dim` reported only propext,
Classical.choice, and Quot.sound. The probe compiled without warnings in 1.8 s.

## Status

landed 20261020T132041-L-1406898 2026-10-20 (merge of deliver/T3/Sheaf.AlgebraicGeometry.BaseChangeDimension)
