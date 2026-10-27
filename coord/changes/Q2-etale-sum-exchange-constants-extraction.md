# AlgebraicGeometry.Etale.etaleSumExchangeConstantIso

## Reason

The complete six-conjunct proof exceeded 60 seconds in one file. Profiling isolated the
constant construction (about 12 seconds in the kernel) and the independent constants square
(about 34 seconds even after using abstract exact-single/naturality helpers). The mate proof
adds further kernel work. Concrete projection-normalization alternatives were slower.
Separate the unchanged constant construction, the fully proved constants square, and the
mate/counit argument into independently checked modules. No hole is introduced.

The construction's signature and body below are verbatim. Its full Lean name is unchanged;
the item publicly imports its new module. Every original public import is retained. No
existing declaration is weakened, renamed or given a different attribute. Thus the canonical
isomorphism and every target's meaning are unchanged. The definition is real data composed
from the existing exact-single and constant-sheaf isomorphisms.

## Old

In `Sheaf.AlgebraicGeometry.EtaleSumExchangeCounit`:

```lean
noncomputable def etaleSumExchangeConstantIso
    (A : Type (u + 1)) [CommRing A] {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)) :=
  ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A))
```

## New

In `Sheaf.AlgebraicGeometry.EtaleSumExchangeConstantIso`:

```lean
noncomputable def etaleSumExchangeConstantIso
    (A : Type (u + 1)) [CommRing A] {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)) :=
  ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A))
```

The original module adds
`public import Sheaf.AlgebraicGeometry.EtaleSumExchangeConstantIso`.
The private proof import `Sheaf.AlgebraicGeometry.EtaleSumExchangeConstants` supplies the
proved final conjunct. Its public theorem `etaleSumExchangeConstantSquare` is exactly the
constant-square step for arbitrary commutative rings and arbitrary scheme morphisms.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleSumExchangeCounit | Q2 | Publicly re-exports the unchanged constant definition and proves the original theorem. |
| Sheaf.AlgebraicGeometry.EtaleSumExchangeConstantIso | Q2, new | Owns the unchanged construction. |
| Sheaf.AlgebraicGeometry.EtaleSumExchangeConstants | Q2, new | Proves the constants square using the unchanged construction. |
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | unclaimed | Unchanged direct importer; uses the original derived-counit conjunct. |
| Sheaf.AlgebraicGeometry.EtaleSupportExchangeRightMate | unclaimed | Unchanged direct importer; uses the original derived-counit conjunct. |

`tools/downstream.py --uses etaleSumExchangeConstantIso` finds only the original item
mentioning the definition among its 5,588 transitive downstream modules. The two direct
importers compiled unchanged against the delivery, in 35.7 and 36.0 seconds respectively.
Their temporary copies have been removed; no consumer adaptation is needed.

## Status

landed 20261027T021348-L-2761990 2026-10-27 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.EtaleSumExchangeCounit)
