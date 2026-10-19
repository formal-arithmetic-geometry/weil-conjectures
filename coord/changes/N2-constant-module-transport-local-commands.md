# commutativeSiteConstantModuleFunctor_transport

## Reason

The transport proof needs private comparison maps for module sheafification. A local
section abstracts the sheafification instances and the commuting coefficient triangle.
Local irreducibility attributes keep elaboration from unfolding the constructed maps
after their underlying abelian-sheaf maps have been identified. The static interface
check records these variable and attribute commands, so this record documents them.
All existing public signatures, definitions, instances and public imports are identical.

## Old

The only variable command was:

```lean
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
```

There was no Transport section, no private comparison construction, and no local
irreducibility attribute. The four public auxiliary theorem proofs were `by sorry`.

## New

The original variable command remains. The additional commands, verbatim, are:

```lean
section Transport

variable [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {R₀ : Cᵒᵖ ⥤ RingCat.{max u v}} {A B : Sheaf J RingCat.{max u v}}
  (ηA : R₀ ⟶ A.obj) (ηB : R₀ ⟶ B.obj)
  [Presheaf.IsLocallyInjective J ηA] [Presheaf.IsLocallySurjective J ηA]
  [Presheaf.IsLocallyInjective J ηB] [Presheaf.IsLocallySurjective J ηB]
  (α : A ⟶ B) (hsq : ηA ≫ α.hom = ηB)
```

The section contains only private declarations. Before the private theorem about the
seed's underlying map, the unused instances are omitted:

```lean
omit [Presheaf.IsLocallyInjective J ηA] [Presheaf.IsLocallySurjective J ηA] in
```

After proving the underlying-map formulas, the private definitions are marked locally:

```lean
attribute [local irreducible] moduleSheafificationSeed
attribute [local irreducible] moduleSheafificationComparison
```

The section closes with `end Transport` before the existing public transport theorem.
The local attributes end with that section; the variables do not add hypotheses to any
public declaration. The four auxiliary theorem proofs are now complete. No public
definition acquires a private dependency.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor | N2 | Four proofs completed; private helper constructions and scoped commands added. |

Ran `tools/downstream.py Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
--uses realizationRingIso_fac moduleSheafificationSeed moduleSheafificationSeed_toPresheaf
moduleSheafificationComparison moduleSheafificationComparison_toSheaf
moduleSheafificationComparison_isIso`. It found 424 downstream modules and zero users
of each private helper. No downstream module is adapted. The public contract and all
target meanings are unchanged, so no target statement review is reopened.

## Status

landed 20261019T005349-L-2758145 2026-10-19 (merge of deliver/N2/Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor)
