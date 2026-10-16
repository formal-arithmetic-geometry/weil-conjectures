# constructibleToQbar_pullback_cube

## Reason

The preflight conservatively classifies added `section`, `variable`, `open`, and local
reducibility commands as an interface change. This record documents those commands.
They support proved private projection/coherence helpers; every existing declaration
signature, public import, and comparison definition is unchanged. The original public
statement is reproduced below, identically in Old and New. No target meaning changes
and no semantic target review is reopened.

The proof-only imports expose existing private generic calculations inside this module.
The added `open CategoryTheory.MonoidalCategory` is a local name-resolution command.
The new `RestrictionAPI` and `PullSquareCalculation` sections delimit helper variables
and reducibility settings. All added reducibility attributes are `[local irreducible]`;
none is exported. The elaboration options choose transparency and a heartbeat budget,
without changing any term, kernel check, or downstream instance registration.

## Old

```lean
theorem constructibleToQbar_pullback_cube
    (sq : CommSq g' f' f g) (V : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToQbarPullIso ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj V)).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison
          (Profinite.continuousMapRingObj E) ℓ k sq).hom.app V) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f).obj V)).hom =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarPullIso ℓ k E g V).hom ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ)
        ℓ k sq).hom.app ((constructibleToPadicAlgCl Y ℓ E).obj V) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').map
        (constructibleToQbarPullIso ℓ k E f V).inv
```

## New

```lean
theorem constructibleToQbar_pullback_cube
    (sq : CommSq g' f' f g) (V : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToQbarPullIso ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj V)).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison
          (Profinite.continuousMapRingObj E) ℓ k sq).hom.app V) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f).obj V)).hom =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarPullIso ℓ k E g V).hom ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ)
        ℓ k sq).hom.app ((constructibleToPadicAlgCl Y ℓ E).obj V) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').map
        (constructibleToQbarPullIso ℓ k E f V).inv
```

New proof-local commands include:

```lean
open CategoryTheory.MonoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] monoidal_pointUpperStar monoidal_upperStarFromPoint
  pointUpperStarLowerStarAdjunction
-- Inside PullSquareCalculation only:
attribute [local irreducible] constructibleToPadicAlgCl constructibleToQbarPullIso
  boundedConstructibleUpperStar boundedConstructibleLowerStar
```

## Users

`tools/downstream.py Sheaf.Paper.CondensedQbarPullbackCube --uses
constructibleToQbar_pullback_cube` lists seven downstream modules, with the direct use
in `CondensedQbarExchangeLeftAdjunct`. Their statements and definitions retain exactly
the same meaning. No consumer is adapted. The unchanged direct consumer compiled in 39.8 seconds against
the delivered module, which compiled with artifacts in 57.6 seconds. Holders were read
from the claim files.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarPullbackCube | D4 | Sole original hole proved; existing public statement preserved. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Direct theorem user; source unchanged, consumer compile checked. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Transitive theorem user; no signature or meaning change. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Transitive theorem user; no signature or meaning change. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No signature or meaning change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No signature or meaning change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No signature or meaning change. |
| TargetsCheck | unclaimed | Target signatures and their definitions unchanged. |

## Status

landed 20261016T104121-L-2376737 2026-10-16 (merge of deliver/D4/Sheaf.Paper.CondensedQbarPullbackCube)
