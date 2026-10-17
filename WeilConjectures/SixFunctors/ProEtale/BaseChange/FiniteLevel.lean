/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Torsion
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.Transport

/-!
# Proper base change on classical pro-étale complexes

Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, and a commutative ring `Λ`. For a pro-étale complex `K` on `X` equipped
with an étale-origin witness `(L, α)`, `L ∈ D⁺(X_ét, Λ)` and `α : ν_X^* L ≅ K`, whose
cohomology sheaves are torsion abelian sheaves, the pro-étale exchange map
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism (blueprint `sk-thm-properbasechange`,
`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper_of_isTorsion`). It is
obtained by conjugating the étale proper base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`) by the site
comparison, as recorded by the transport lemma
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`. For a finite ring `Λ` the torsion
hypothesis is automatic (blueprint `thm-weil-pbc-finite-level-proetale`).

The ambient pro-étale exchange transformation (blueprint
`def-weil-pbc-ambient-ringed-exchange`) is `AlgebraicGeometry.ProEtale.derivedBaseChangeMap`;
the mate of a transformation under two adjunctions (blueprint `def-weil-pbc-adjunction-mate`)
is `CategoryTheory.mateEquiv`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Blueprint `sk-thm-properbasechange`: **proper base change on classical pro-étale
complexes**. Let `Λ` be any commutative ring and take a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper and `g` arbitrary. Let `K` be a classical pro-étale complex on `X`, i.e. one
equipped with an étale-origin witness `α : ν_X^* L ≅ K` with `L ∈ D⁺(X_ét, Λ)` (blueprint
`def-weil-pbc-etale-origin-witness`), whose cohomology sheaves are torsion as abelian sheaves.
Then the pro-étale exchange map `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` (blueprint
`def-weil-pbc-ambient-ringed-exchange`) is an isomorphism.

The torsion hypothesis on `K = ν_X^* L` descends to the cohomology sheaves of `L`
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf.of_isTorsion_comparisonUpperStar`, using that
`ν_X^*` is exact); the étale proper base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`) is then transported
to the pro-étale site by `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`
(blueprint `lem-weil-pbc-transport-identifies-exchange`). -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_isProper_of_isTorsion [IsProper f]
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (α : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K)
    (hK : ∀ n : ℤ, ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.homologyFunctor _ n).obj K)).IsTorsion) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ α]
  have hL : Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X L := fun n ↦
    IsTorsionModuleSheaf.of_isTorsion_comparisonUpperStar _
      (Sheaf.IsTorsion.of_iso ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
          ((DerivedCategory.homologyFunctor _ n).mapIso α.symm ≪≫
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryHomologyFunctorIso
              n).symm.app (DerivedCategory.Plus.ι.obj L))) (hK n))
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    exact Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq L hL
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq.flip
    inferInstance
  have : QuasiSeparated f' :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq.flip inferInstance
  have hαβ := ProEtale.comparison_derivedBaseChangeMap Λ sq L
  have : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((ProEtale.baseChangeSourceComparisonIso f g Λ).app L)
      ((ProEtale.baseChangeTargetComparisonIso g' f' Λ).app L) hαβ.symm)).1 this

/-- Blueprint `thm-weil-pbc-finite-level-proetale`: for a cartesian square with `f` proper, a
finite coefficient ring `Λ` and a pro-étale complex `K` on `X` with an étale-origin witness
`(L, α)`, `α : ν_X^* L ≅ K` with `L ∈ D⁺(X_ét, Λ)`, the pro-étale exchange map
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism. This is the special case of
`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper_of_isTorsion`
(blueprint `sk-thm-properbasechange`) where all sheaves of `Λ`-modules are torsion. -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_isProper_of_finite [Finite Λ] [IsProper f]
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (α : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  isIso_derivedBaseChangeMap_app_of_isProper_of_isTorsion Λ sq L K α fun _ ↦
    Sheaf.IsTorsion.of_forall_isAddTorsion fun _ ↦
      IsAddTorsion.module_of_torsion Λ _ isAddTorsion_of_finite

end AlgebraicGeometry
