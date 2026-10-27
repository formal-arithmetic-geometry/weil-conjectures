# AlgebraicGeometry.Scheme.finite_fiber_faithful and eq_of_finite_fiber

## Reason

Repair the return for K7 at c5abafba593. The finite lifting and reconstruction
proofs duplicated an existing private theorem of the unclaimed
`Sheaf.Paper.LatticeNormalizationRationalExact`. Promote its two finite-stalk
faithfulness helpers to public visibility in place and import them. This removes
the duplicates instead of renaming them or changing their propositions.

## Old

```lean
private theorem finite_fiber_faithful {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group) :
    (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := T)) ⋙
      (pointSmallEtale p.point).sheafFiber (A := Type (u + 1))).Faithful
```

```lean
private theorem eq_of_finite_fiber {T : Scheme.{u}}
    (p : SfMonodromyPoint T) (c : GaloisLisseFiniteCorrespondence p.point p.group)
    {R : Type (u + 1)} [CommRing R]
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F))
    (hG : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R G))
    (f g : F ⟶ G)
    (h : ((pointSmallEtale p.point).sheafFiber.map f) =
      ((pointSmallEtale p.point).sheafFiber.map g)) : f = g
```

## New

```lean
theorem finite_fiber_faithful {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group) :
    (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := T)) ⋙
      (pointSmallEtale p.point).sheafFiber (A := Type (u + 1))).Faithful
```

```lean
theorem eq_of_finite_fiber {T : Scheme.{u}}
    (p : SfMonodromyPoint T) (c : GaloisLisseFiniteCorrespondence p.point p.group)
    {R : Type (u + 1)} [CommRing R]
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F))
    (hG : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R G))
    (f g : F ⟶ G)
    (h : ((pointSmallEtale p.point).sheafFiber.map f) =
      ((pointSmallEtale p.point).sheafFiber.map g)) : f = g
```

Both proof terms are retained verbatim. Added docstrings explain the source
and argument. Existing public declarations and public imports stay unchanged.

## Users

`tools/downstream.py ... --uses` found only internal uses of each helper in the
original module. Its six downstream modules are also listed below. No original
consumer depended on the private names; making them available adds an API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LatticeNormalizationRationalExact | unclaimed | Promote two proved helpers; their types and proof terms are identical. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | unclaimed | No edits; existing declarations and interfaces remain identical. |
| Sheaf.Paper.EtaleLocalMonodromyRealizationBase | unclaimed | No edits; existing declarations and interfaces remain identical. |
| Sheaf.Paper.IntegralFibreMonodromyReconstruction | K7 | Remove both private duplicates; import and use the shared helpers. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | No edits; existing declarations and interfaces remain identical. |
| Sheaf.Paper.NormalizedMonodromyExact | unclaimed | No edits; existing declarations and interfaces remain identical. |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | No edits; existing declarations and interfaces remain identical. |
| Sheaf.Paper.FiniteFibreLinearLifting | unclaimed | Remove private duplicate; import and use shared faithfulness. |

## Status

landed 20261024T190243-L-4006348 2026-10-24 (merge of deliver/K7/Sheaf.Paper.IntegralFibreMonodromyReconstruction)
