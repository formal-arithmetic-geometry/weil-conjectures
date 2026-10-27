# CategoryTheory.RingedEquivalenceTensorDescent: native instance caches

## Reason

The complete descent proof repeatedly synthesizes native module-sheaf structures through
coefficient-universe sheafification. Reusing explicitly typed abbreviations avoids repeating
that search. These abbreviations contain the existing native instances, constructed by
`inferInstance`; they introduce neither a new choice of tensor nor a new sheaf category.
They are local instances only within the item module.

## Old

No cache declarations existed. The module synthesized the native instances directly.

## New

The module adds these reducible native-instance caches:

```lean
abbrev countableHomotopyMonoidal : MonoidalCategory (HomotopyCategory B (.up ℤ)) :=
  inferInstance
abbrev countableHomotopyBraided : BraidedCategory (HomotopyCategory B (.up ℤ)) :=
  inferInstance
abbrev ringedForgetSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance
abbrev ringedWeakSheafify : HasWeakSheafify J AddCommGrpCat.{r} := inferInstance
abbrev ringedModuleAbelian : Abelian (Modules R) := inferInstance
abbrev ringedModuleMonoidal : MonoidalCategory (Modules R) := inferInstance
abbrev ringedModuleMonoidalPreadditive : MonoidalPreadditive (Modules R) := inferInstance
abbrev ringedModuleSymmetric : SymmetricCategory (Modules R) := inferInstance
abbrev ringedModuleCoproducts : HasCountableCoproducts (Modules R) := inferInstance
```

Each receives a local instance attribute of priority 12000. The existing
`countableCochainMonoidal` instance also receives this priority locally;
`ringedCochainMonoidal` receives priority 12001 locally. Their values and public
instance priorities are unchanged. The existing graded tensor instances also receive
priority 12000 locally. The new private `modelIdentity` construction is marked irreducible
after its unit and tensor equations have been proved, and its later users use these equations. These abbreviations are
fully constructed from existing instances, with no existence theorem or postponed data.
Existing signatures and definitions retain their meanings and are definitionally compatible.
No source-library module is changed. No consumer adaptation is needed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RingedEquivalenceResolvingTensorDescent | K8 | Reuses existing instances during elaboration. |
| Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification | unclaimed; no adaptation | Existing private import and public interfaces remain compatible. |

The downstream query lists only the constant-module identification module. None of the new
names previously existed, so they have no existing name-based users. Target statements are
unchanged, and these cache abbreviations do not change any target definition.

## Status

landed 20261023T135023-L-2825679 2026-10-23 (merge of deliver/K8/Sheaf.Algebra.Homology.RingedEquivalenceResolvingTensorDescent)
