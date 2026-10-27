# WeilConjectures.ConstructibleExceptionalCoefficients.rawRationalFunctor

## Reason

Profiling showed repeated additive and linear instance synthesis for the same full integral
functor while elaborating its tensor extension. Bind that functor once and cache those two
proof instances locally before constructing the functor. Zeta reduction and proof irrelevance
recover the previous definition: the object map is still the same full integral image and
the arrow map is still the same linear base change. There is no change to its signature,
public attributes, or the mathematical coefficient categories.

The proof also uses local irreducibility attributes for the raw functor and comparison to
avoid unfolding tensor constructions during generic categorical reasoning. These attributes
are scoped to the item and are not exported to consumers.

## Old

```lean
def rawRationalFunctor
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    C.{u, v} l Ω X (.rational E) ⥤ C.{u, v} l Ω Y (.rational E) where
  obj K := ⟨(fullIntegralFunctor l Ω E X Y F h).obj K.obj⟩
  map f := ((fullIntegralFunctor l Ω E X Y F h).mapLinearMap
    (Padic.coefficientExtensionIntegers l E.carrier)).baseChange
      (Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) f
  map_id K := (rawTensorFunctorLaws _ (fullIntegralFunctor l Ω E X Y F h)).1 K.obj
  map_comp f g := (rawTensorFunctorLaws _ (fullIntegralFunctor l Ω E X Y F h)).2 _ _ _ f g
```

## New

```lean
def rawRationalFunctor
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (h : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X) :
    C.{u, v} l Ω X (.rational E) ⥤ C.{u, v} l Ω Y (.rational E) := by
  let H := fullIntegralFunctor l Ω E X Y F h
  have : H.Additive := fullIntegralFunctorAdditive l Ω E X Y F h
  have : H.Linear (Padic.coefficientExtensionIntegers l E.carrier) :=
    fullIntegralFunctorLinear l Ω E X Y F h
  exact {
    obj := fun K ↦ ⟨H.obj K.obj⟩
    map := fun f ↦ (H.mapLinearMap (Padic.coefficientExtensionIntegers l E.carrier)).baseChange
      (Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) f
    map_id := fun K ↦ (rawTensorFunctorLaws _ H).1 K.obj
    map_comp := fun f g ↦ (rawTensorFunctorLaws _ H).2 _ _ _ f g }
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization | C4 | Definitionally identical tensor maps; cached proof instances speed elaboration. |
| Sheaf.Paper.ExceptionalScalarMateLocalization | unclaimed in shared snapshot | Sole direct importer; existing public definitions and statements remain compatible. |
| Sheaf.Paper.ExceptionalRationalStageLocalization | unclaimed in shared snapshot | Only external textual user of rawRationalFunctor; its additive proof and tensor-map computation remain definitionally identical. |

The direct importer and the external textual user are checked against the delivered module.
Other indirect importers mention neither changed declaration. All target statements retain
the same definitions up to definitional equality.

## Status

landed 20261027T180508-L-3867217 2026-10-27 (merge of deliver/C4/Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization)
