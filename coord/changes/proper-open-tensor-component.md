# AlgebraicGeometry.ProEtale.properOpenTensorIso

## Reason

Select the inverse component of the published natural isomorphism directly. The previous
`asIso` construction recovered that inverse through typeclass inference, causing expensive
unfolding when the inverse appeared in tensor/composition proofs. The new forward map is
identical, and uniqueness of inverses identifies the inverse maps. The signature and all
normalizations remain unchanged.

## Old

```lean
noncomputable def properOpenTensorIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    ((ProperOpenTensor Λ X).obj ((ProperOpenShriek Λ j).obj M)).obj N ≅
      (ProperOpenShriek Λ j).obj
        (((ProperOpenTensor Λ U).obj M).obj ((ProperOpenPull Λ j).obj N)) :=
  asIso (((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} Λ) j).inv.app M).app N)
```

## New

```lean
noncomputable def properOpenTensorIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ProperOpenDerived Λ U) (N : ProperOpenDerived Λ X) :
    ((ProperOpenTensor Λ X).obj ((ProperOpenShriek Λ j).obj M)).obj N ≅
      (ProperOpenShriek Λ j).obj
        (((ProperOpenTensor Λ U).obj M).obj ((ProperOpenPull Λ j).obj N)) :=
  (((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} Λ) j).app M).app N).symm
```

## Users

`tools/downstream.py Sheaf.SixFunctors.ProperOpenProjectionMate --uses properOpenTensorIso`
reported the five direct users below. No statement changes: both versions select the same
isomorphism, by equality of forward maps and uniqueness of inverses.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | inverse components reduce directly |
| Sheaf.Paper.ForwardProductCoordinateTransport | T1 | same forward component |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | same forward component |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | same forward component |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | same forward component |

All other downstream modules see the same declarations and maps. No target type changes.

## Status

landed 20261026T023342-L-546669 2026-10-26 (merge of deliver/J3/Sheaf.SixFunctors.ProperOpenProjectionMate)
