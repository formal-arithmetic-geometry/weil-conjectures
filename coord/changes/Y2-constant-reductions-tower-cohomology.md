# AlgebraicGeometry.Scheme.mlTowerCohomology

## Reason

Name the same standard diagram-category homology functor on an abstract small site
before using it at the coefficient-sized scheme site. Its implementation is fully
constructed and marked irreducible so inference does not expand sheafification
instances during finite-model assembly. The scheme API specializes this implementation.
This is the same functor with the same standard localization and actual morphism maps;
no object, hypothesis, universe, or target statement changes.

## Old

```lean
abbrev mlTowerCohomology {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    ConstantCompletion.TD R ⥤ (ℕᵒᵖ ⥤ ConstantCompletion.Mod R) :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q
```

## New

```lean
abbrev mlTowerCohomology {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    ConstantCompletion.TD R ⥤ (ℕᵒᵖ ⥤ ConstantCompletion.Mod R) :=
  constantReductionsTowerCohomology R q
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WContractibleConstantReductionsML | Y2 | Same standard cohomology functor through its named implementation. |

The downstream query finds no external Lean users. No source-library declaration changes.

## Status

landed 20261020T230849-L-622677 2026-10-20 (merge of deliver/Y2/Sheaf.Paper.WContractibleConstantReductionsML)
