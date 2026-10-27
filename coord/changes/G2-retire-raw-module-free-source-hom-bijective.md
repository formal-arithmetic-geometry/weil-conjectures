# AlgebraicGeometry.Etale.rawModuleFreeSourceHom_bijective

## Reason

Complete the explicit retirement assignment in coord/retire-items.tsv. The
Sheaf copy has zero sorry holes and duplicates the proved adopted upstream
scalar-comparison theorem. Its only public declaration has the identical
statement after expanding the already established abbreviation
RawModuleScalarComparison.forget to moduleAbelianForget.

The current source supersedes the inventory's two historical Sheaf consumers:
they are absent from lean/ and quarantine/, and their mathematical nodes already
point to the two upstream consumers. Both upstream consumers import and apply
the upstream free-source theorem. This delivery preserves that actual argument;
it does not infer mathematical irrelevance from zero Lean importers.

## Old

Module: Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective.

```lean
theorem rawModuleFreeSourceHom_bijective
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun g :
        (upperStar (ModuleCat.{u + 1} Λ) f).obj ((freeSheaf Λ S).obj U) ⟶ M ↦
      ((upperStar AddCommGrpCat.{u + 1} f).map
          (RawModuleScalarComparison.freeMap Λ S U) ≫
        RawModuleScalarComparison.pullback Λ f ((freeSheaf Λ S).obj U)) ≫
          (RawModuleScalarComparison.forget Λ X).map g)
```

The module publicly imports
Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso and proves the theorem
using four private helpers: abelianSections, abelianSections_comp,
freeMap_sections and scalar_unit. None is external API.

## New

Withdraw the duplicate Sheaf module through deleted.txt. Attach
lem-sbc-raw-module-free-source-hom-bijective to the existing, proved theorem in
WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceHomBijective:

```lean
theorem rawModuleFreeSourceHom_bijective
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun g :
        (upperStar (ModuleCat.{u + 1} Λ) f).obj ((freeSheaf Λ S).obj U) ⟶ M ↦
      ((upperStar AddCommGrpCat.{u + 1} f).map
          (RawModuleScalarComparison.freeMap Λ S U) ≫
        RawModuleScalarComparison.pullback Λ f ((freeSheaf Λ S).obj U)) ≫
          (moduleAbelianForget Λ X).map g)
```

The complete upstream proof identifies both Hom sets with the same group of
sections through inverse-image adjunctions, sheafification, free adjunctions and
Yoneda. Its private freeMap_sections and scalar_unit computations identify the
explicit comparison map with the resulting equivalence. No hypothesis is added
or removed, including universes and arbitrary commutative rings and schemes.
The abbreviation expansion is the only signature-text difference; the scratch
probe proves the complete old signature by applying the upstream theorem.

No upstream file is edited. The node statement, proof, proof dependencies,
parent dependencies and owning unit's realized lists retain their content.
There is no change of target meaning or public mathematical definition.

## Users

The downstream tool reports zero modules importing the Sheaf copy. Independent
searches of all live Lean sources and quarantine/ likewise find no importer or
caller relying on its declaration. The only matching declaration outside the
item is the upstream theorem, used by the two upstream modules below. The
library's upstream root also imports that upstream module, never the Sheaf copy.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective | G2 | Withdraw duplicate; retarget its node to the proved upstream theorem. |
| WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceHomBijective | unclaimed | Existing replacement theorem and all upstream source remain unchanged. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapInjective | unclaimed | Already imports and applies the upstream theorem; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapSurjective | unclaimed | Already imports and applies the upstream theorem; no adaptation required. |

The absent historical Sheaf consumers are not restored or deleted. Neither has
a matching rework/quarantine row requiring restoration. The two parent nodes
continue to cite lem-sbc-raw-module-free-source-hom-bijective. No DAG node or
mathematical proof dependency is withdrawn.

Validation: scratchpad/VerifyCanonicalComparison.lean compiled through
lcompile.py in 8.4 seconds. The example states the complete old signature
and proves it with the upstream theorem. The same probe imports both actual
upstream parents and prints axioms for rawModuleFreeSourceHom_bijective,
rawModuleAbelianHomMap_injective and rawModuleAbelianHomMap_surjective:
exactly propext, Classical.choice and Quot.sound for each, with no sorryAx.

## Status

landed 20261025T051845-L-4165597 2026-10-25 (merge of deliver/G2/Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective)
