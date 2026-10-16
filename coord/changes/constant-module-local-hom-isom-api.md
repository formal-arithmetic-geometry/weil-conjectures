# Constant-module local Hom and Isom APIs

## Reason

Prove `CategoryTheory.siteConstantModule_isomSheaf` without adding holes. Every existing signature remains identical; eight new supporting modules construct local Hom/Isom and prove their gluing and finite-presentation comparison properties. These are additions, with no repair or adaptation of another group’s module.

## Old

The eight modules listed below, and all their declarations, were absent. No existing definition or statement is replaced. The signature of `CategoryTheory.siteConstantModule_isomSheaf` is unchanged.

## New

The new files contain the complete constructions and proofs. Their principal declarations are:

`Sheaf.CategoryTheory.ConstantLocalModuleHom`:

```lean
theorem constantLocalIso_locallyBijective [Presheaf.IsLocallyInjective J (constantLocalHom F M N)] [Presheaf.IsLocallySurjective J (constantLocalHom F M N)] [Presheaf.IsLocallySurjective J (constantLocalHom F N M)] [Presheaf.IsLocallyInjective J (constantLocalHom F M M)] [Presheaf.IsLocallyInjective J (constantLocalHom F N N)] : Presheaf.IsLocallyInjective J (constantLocalIso F M N) ∧ Presheaf.IsLocallySurjective J (constantLocalIso F M N)
```

`Sheaf.CategoryTheory.FinitePresentationLocalLift`:

```lean
theorem finitePresentation_linearLiftSieve_mem [Module.FinitePresentation Λ M] [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η] {U : Cᵒᵖ} (a : M ⟶ P.obj U) : linearLiftSieve η a ∈ J U.unop
```

`Sheaf.CategoryTheory.LocalModuleHom`:

```lean
theorem localHom_isSheaf : Presheaf.IsSheaf J (localHom M N)
```

`Sheaf.CategoryTheory.LocalModuleIso`:

```lean
theorem localIso_isSheaf : Presheaf.IsSheaf J (localIso M N)
```

`Sheaf.CategoryTheory.SiteConstantModuleHomInjective`:

```lean
theorem siteConstantModuleHom_locallyInjective {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] (M N : ModuleCat.{u} Λ) [Module.Finite Λ M] : Presheaf.IsLocallyInjective J (SheafOfModules.constantLocalHom (siteConstantModuleFunctor J Λ) M N)
```

`Sheaf.CategoryTheory.SiteConstantModuleHomSurjective`:

```lean
theorem siteConstantModuleHom_locallySurjective {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ] (M N : ModuleCat.{u} Λ) [Module.FinitePresentation Λ M] : Presheaf.IsLocallySurjective J (SheafOfModules.constantLocalHom (siteConstantModuleFunctor J Λ) M N)
```

`Sheaf.CategoryTheory.SiteConstantModuleOverHom`:

```lean
theorem siteConstantModule_over_hom_ext (U : C) (a b : ((siteConstantModuleFunctor J Λ).obj M).over U ⟶ ((siteConstantModuleFunctor J Λ).obj N).over U) (h : ∀ x : M, a.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) x) = b.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) x)) : a = b
```

`Sheaf.CategoryTheory.SiteConstantModuleUnit`:

```lean
theorem siteConstantModuleUnitSections_locallyBijective (M : ModuleCat.{u} Λ) : Presheaf.IsLocallyInjective J (siteConstantModuleUnitSections J Λ M) ∧ Presheaf.IsLocallySurjective J (siteConstantModuleUnitSections J Λ M)
```

The files also define the named local Hom/Isom presheaves, their equivalence with actual slice maps, composition and restriction laws, constant-section transformations, and the linear constant-module unit. All data are constructed explicitly; all accompanying proof fields are proved. The Hom comparison modules publicly import the constant-module functor needed in their statements and privately import the unit construction used in their proofs. The injectivity module imports only finite-generation definitions, rather than finite-presentation theory.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.ConstantLocalModuleHom` | E4 (new support or assigned item) | Uses new API from `Sheaf.CategoryTheory.LocalModuleIso`; compiles. |
| `Sheaf.CategoryTheory.LocalModuleIso` | E4 (new support or assigned item) | Uses new API from `Sheaf.CategoryTheory.LocalModuleHom`; compiles. |
| `Sheaf.CategoryTheory.SiteConstantModuleHomInjective` | E4 (new support or assigned item) | Uses new API from `Sheaf.CategoryTheory.ConstantLocalModuleHom`, `Sheaf.CategoryTheory.SiteConstantModuleUnit`; compiles. |
| `Sheaf.CategoryTheory.SiteConstantModuleHomSurjective` | E4 (new support or assigned item) | Uses new API from `Sheaf.CategoryTheory.ConstantLocalModuleHom`, `Sheaf.CategoryTheory.SiteConstantModuleUnit`, `Sheaf.CategoryTheory.SiteConstantModuleOverHom`, `Sheaf.CategoryTheory.FinitePresentationLocalLift`; compiles. |
| `Sheaf.CategoryTheory.SiteConstantModuleIsomSheaf` | E4 (new support or assigned item) | Uses new API from `Sheaf.CategoryTheory.SiteConstantModuleHomInjective`, `Sheaf.CategoryTheory.SiteConstantModuleHomSurjective`; compiles. |
| `Sheaf.CategoryTheory.SiteConstantModuleOverHom` | E4 (new support or assigned item) | Uses new API from `Sheaf.CategoryTheory.SiteConstantModuleUnit`; compiles. |
| `Sheaf.Paper.ProEtaleLisseOrigin` | D3 | Existing direct importer. No changes; original source compiled against the new main module. |

No prior user can mention the new declarations. `tools/downstream.py Sheaf.CategoryTheory.SiteConstantModuleIsomSheaf --uses siteConstantModule_isomSheaf` finds no external textual user of the theorem yet. Its existing direct importer above retains the same public interface.

## Status

landed 20261016T131234-L-3106505 2026-10-16 (merge of deliver/E4/Sheaf.CategoryTheory.SiteConstantModuleIsomSheaf)
