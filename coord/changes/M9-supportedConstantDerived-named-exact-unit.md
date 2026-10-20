# supportedConstantDerived

## Reason

Keep the canonical degree-zero object and complete exact derived unit behind named
irreducible functions. The original raw projections force Lean to normalize the
localization/Shrink construction when specializing coherence lemmas, exceeding the
60-second compile limit. This is a representation change: `obj` is precisely the
same single-functor object, and `unit` is precisely the same single map followed
by the inverse exact-single comparison. No mathematical data is replaced.

## Old

```lean
noncomputable def supportedConstantDerived {A : Type (u + 1)} [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.singleFunctor
    (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
    (supportedConstantModule i)
```

## New

```lean
noncomputable def supportedConstantDerived {A : Type (u + 1)} [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  SheafExactDegreeZero.scalarObj Z.smallEtaleTopology A (supportedConstantModule i)
```

## Users

`tools/downstream.py Sheaf.SixFunctors.GeoCartierCoeffExtension --uses supportedConstantDerived`
found 654 transitive importers and only the following declaration user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | M9 | Same object/morphism, now through the named canonical interface; the existing theorem signature is unchanged. |

No consumer adaptation is needed. Any target whose definitions transitively use
this declaration should receive the normal statement-meaning review; the
represented construction and its normalization are unchanged.

## Status

landed 20261020T230814-L-615093 2026-10-20 (merge of deliver/M9/Sheaf.SixFunctors.GeoCartierCoeffExtension)
