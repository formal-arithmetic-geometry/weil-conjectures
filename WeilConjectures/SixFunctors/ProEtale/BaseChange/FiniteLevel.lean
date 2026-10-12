/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProperTorsion
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.Transport

/-!
# Finite-level pro-étale proper base change

Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, and a finite coefficient ring `Λ`. For a pro-étale complex `K` on `X` equipped
with an étale-origin witness `(L, α)`, `L ∈ D⁺(X_ét, Λ)` and `α : ν_X^* L ≅ K`, the pro-étale
exchange map `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism (blueprint
`thm-weil-pbc-finite-level-proetale`). It is obtained by conjugating the bounded below étale
proper base change isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_of_isProper`) by the site
comparison, as recorded by the transport lemma
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`.

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

/-- Blueprint `thm-weil-pbc-finite-level-proetale`: for a cartesian square with `f` proper, a
finite coefficient ring `Λ` and a pro-étale complex `K` on `X` with an étale-origin witness
`(L, α)`, `α : ν_X^* L ≅ K` with `L ∈ D⁺(X_ét, Λ)`, the pro-étale exchange map
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism. The witness only enters through the
isomorphism class of `K`, so the statement is independent of the choice of witness. -/
theorem ProEtale.isIso_derivedBaseChangeMap_app_of_isProper [Finite Λ] [IsProper f]
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (α : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      (DerivedCategory.Plus.ι.obj L) ≅ K) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ α]
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    exact Etale.isIso_derivedBaseChangeMapPlus_app_of_isProper Λ sq L
      (Etale.DerivedCategory.Plus.torsionHomology_of_isTorsion Λ X isAddTorsion_of_finite L)
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

end AlgebraicGeometry
