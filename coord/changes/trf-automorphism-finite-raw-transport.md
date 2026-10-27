# WeilConjectures.trfAutomorphismFiniteRaw

## Reason

Specialize the same explicit raw module transport constructor used by the system
functor. This removes the redundant restriction through an identity coefficient
map in finite tensor evaluation. The input and output coefficient sheaves,
sections, restrictions, scalar actions and maps are unchanged.

## Old

```lean
def trfAutomorphismFiniteRaw (n : ℕ) :
    normalizedDVRModules l E S n ⥤
      ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj
              (integralCoefficientCommRingSheaf l E S n))) :=
  SheafOfModules.pushforward (F := proEtaleIsoPostcompose g) (𝟙 _)

```

## New

```lean
def trfAutomorphismFiniteRaw (n : ℕ) :
    normalizedDVRModules l E S n ⥤
      ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj
              (integralCoefficientCommRingSheaf l E S n))) :=
  trfRawModuleTransport (proEtaleIsoPostcompose g) (integralCoefficientSheaf l E S n)

```

## Users

There are no modules downstream of the item. Finite tensor and its evaluation
statement are its only consumers; both are compiled in the same file.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.AutomorphismTensorReductionComparison | S1 | Same finite raw transport, sharing trfRawModuleTransport. |

## Status

landed 20261026T070924-L-3699055 2026-10-26 (merge of deliver/S1/Sheaf.TraceFormula.AutomorphismTensorReductionComparison)
