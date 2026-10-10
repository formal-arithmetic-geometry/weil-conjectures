/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# Exchanging an extension by zero with a derived pushforward

For a cartesian square of schemes

```
  U' --j'--> Z'
  |          |
  g'         g''
  ↓          ↓
  U  --j---> Z
```

with `j` and `j'` open immersions, there is a natural exchange map
`Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` on unbounded derived categories of étale sheaves. It is the
mate, along the adjunctions `D(g'^*) ⊣ Rg'_*` and `D(g''^*) ⊣ Rg''_*`, of the inverse of the
derived base change isomorphism `D(g'^*) ⋙ Dj'_! ≅ Dj_! ⋙ D(g''^*)` for the extension by zero.
Since the pullbacks are exact, this needs no monoidal structure on the coefficients.

When `g''` is proper and the coefficients are torsion, this map is an isomorphism; this is the
key step in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange`: the exchange map
  `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_upperStar_map_openImmersionLowerShriekLowerStarExchange_app`:
  for any `g''` and any coefficients, the exchange map is an isomorphism over the open `U`.
- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`:
  with torsion coefficients `Λ` and `g''` proper, the exchange map is an isomorphism.

## TODO

- Redefine `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison` as
  this exchange map for the square `(𝟙 X, c.i, d.i, r.hom)`, whiskered by `R(d.g)_*` and
  composed with `R(𝟙 X)_* ≅ 𝟭` and `R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. Its invertibility then
  follows from that of the exchange map, which removes the `sorry` in
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison` in favour
  of the more general statement. This first needs
  `AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedIso` to be restated as a special
  case of `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

## Blueprint

This file constructs the map of `thm:open-proper-interchange` on unbounded derived categories.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **The exchange map of an extension by zero and a derived pushforward**: for a cartesian
square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the natural
transformation `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`. It is the mate, along the adjunctions
`D(g'^*) ⊣ Rg'_*` and `D(g''^*) ⊣ Rg''_*`, of the inverse of the base change isomorphism
`AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

```
  D(U') --Dj'_!--> D(Z')
   |                 |
  Rg'_*     ⇗      Rg''_*
   ↓                 ↓
  D(U) ---Dj_!---> D(Z)
```

The 2-cell goes from the path `Rg'_*` then `Dj_!` (left, then bottom) to the path `Dj'_!` then
`Rg''_*` (top, then right). (blueprint: the map of `thm:open-proper-interchange`, on unbounded
derived categories) -/
noncomputable def openImmersionLowerShriekLowerStarExchange (hsq : IsPullback g' j' j g'') :
    R((g')_*[A]) ⋙ D((j)_!open[A]) ⟶ D((j')_!open[A]) ⋙ R((g'')_*[A]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction A g')
    (mapDerivedUpperStarLowerStarAdjunction A g'')
    (TwoSquare.mk _ _ _ _
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv)).natTrans

/-- The exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` at `K`, written out: the unit of
`D(g''^*) ⊣ Rg''_*`, then the inverse of the base change isomorphism `bc`, then the counit of
`D(g'^*) ⊣ Rg'_*`.

```
  Dj_! Rg'_* K --η--> Rg''_* Dg''^* Dj_! Rg'_* K --Rg''_*(bc⁻¹)--> Rg''_* Dj'_! Dg'^* Rg'_* K
                                                                          |
                                                                   Rg''_* Dj'_!(ε)
                                                                          ↓
                                                                   Rg''_* Dj'_! K
```
-/
@[reassoc]
lemma openImmersionLowerShriekLowerStarExchange_app (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U'.smallEtaleTopology A)) :
    (openImmersionLowerShriekLowerStarExchange A hsq).app K =
      (mapDerivedUpperStarLowerStarAdjunction A g'').unit.app
          (D((j)_!open[A]).obj (R((g')_*[A]).obj K)) ≫
        R((g'')_*[A]).map
          ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app
              (R((g')_*[A]).obj K) ≫
            D((j')_!open[A]).map ((mapDerivedUpperStarLowerStarAdjunction A g').counit.app K)) := by
  simp [openImmersionLowerShriekLowerStarExchange]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Over the open `U` the exchange map is an isomorphism, for any `g''` and any coefficients:
`D(j^*)` of the exchange map `Dj_! Rg'_* K ⟶ Rg''_* Dj'_! K` is an isomorphism.

By the adjunction `Dj_! ⊣ D(j^*)` it suffices that composing with the exchange map is bijective
on maps out of `Dj_! T`. As `Dj_!` is fully faithful these are the maps `Dj_! ψ` for
`ψ : T ⟶ Rg'_* K`, and composing `Dj_! ψ` with the exchange map and taking the adjoint along
`D(g''^*) ⊣ Rg''_*` gives `bc ≫ Dj'_!(ψ♭)`, with `bc : Dg''^* Dj_! T ≅ Dj'_! Dg'^* T` the base
change isomorphism and `ψ♭ : Dg'^* T ⟶ K` the adjoint of `ψ`; this is bijective in `ψ`, since
`Dj'_!` is fully faithful too. -/
lemma isIso_upperStar_map_openImmersionLowerShriekLowerStarExchange_app
    (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (D((j)^*[ModuleCat.{u + 1} Λ]).map
      ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq).app K)) := by
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let adj' := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j'
  let a' := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g'
  let a'' := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g''
  let bc := mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq
  let α := (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq).app K
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  -- composing with `α` on maps out of `Dj_! T`, followed by the adjunction `Dg''^* ⊣ Rg''_*`
  have key (ψ : T ⟶ R((g')_*[ModuleCat.{u + 1} Λ]).obj K) :
      (a''.homEquiv _ _).symm (D((j)_!open[ModuleCat.{u + 1} Λ]).map ψ ≫ α) =
        bc.inv.app T ≫ D((j')_!open[ModuleCat.{u + 1} Λ]).map ((a'.homEquiv _ _).symm ψ) := by
    rw [show α = _ from openImmersionLowerShriekLowerStarExchange_app _ hsq K]
    erw [← a''.homEquiv_unit]
    rw [a''.homEquiv_naturality_left_symm]
    erw [Equiv.symm_apply_apply]
    rw [a'.homEquiv_counit, Functor.map_comp]
    exact bc.inv.naturality_assoc ψ _
  have h₁ : Function.Bijective (fun ψ : T ⟶ R((g')_*[ModuleCat.{u + 1} Λ]).obj K ↦
      bc.inv.app T ≫ D((j')_!open[ModuleCat.{u + 1} Λ]).map ((a'.homEquiv _ _).symm ψ)) := by
    have := ((Iso.homCongr (bc.app T) (Iso.refl _)).bijective.comp
      (adj'.fullyFaithfulLOfIsIsoUnit.map_bijective _ K)).comp (a'.homEquiv T K).symm.bijective
    convert this using 2
    simp [Iso.homCongr]
  have h₂ : Function.Bijective (fun φ : D((j)_!open[ModuleCat.{u + 1} Λ]).obj T ⟶
      D((j)_!open[ModuleCat.{u + 1} Λ]).obj (R((g')_*[ModuleCat.{u + 1} Λ]).obj K) ↦ φ ≫ α) := by
    rw [← Function.Bijective.of_comp_iff _ (adj.fullyFaithfulLOfIsIsoUnit.map_bijective _ _),
      ← Function.Bijective.of_comp_iff' (a''.homEquiv _ _).symm.bijective]
    convert h₁ using 1
    funext ψ
    exact key ψ
  have := ((adj.homEquiv _ _).bijective.comp h₂).comp (adj.homEquiv _ _).symm.bijective
  convert this using 1
  funext x
  simp [← Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- **Extension by zero commutes with proper pushforward**: if the coefficient ring `Λ` is
torsion as an additive group, then for a cartesian square `g' ≫ j = j' ≫ g''` of schemes with
`j` and `j'` open immersions and `g''` proper, the exchange map
`Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` on the unbounded derived categories `D(-_ét, Λ)` is an
isomorphism.

With `i` the closed complement of `j`, it is checked after `D(j^*)` and after `D(i^*)`:
- after `D(j^*)` this holds for any `g''` and any coefficients, by
  `AlgebraicGeometry.Etale.isIso_upperStar_map_openImmersionLowerShriekLowerStarExchange_app`;
- after `D(i^*)` both sides vanish: the source because `i^* j_! = 0`, and the target by proper
  base change for `g''` along `i`
  (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`),
  since the pullback of `j'_!` to `g''⁻¹(W)`, which does not meet `U'`, vanishes.

(blueprint: unbounded analogue of `thm:open-proper-interchange`) -/
theorem isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring
    (hΛ : IsAddTorsion Λ) [IsProper g''] (hsq : IsPullback g' j' j g'') :
    IsIso (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq) := by
  have hdisj : Disjoint (Set.range j.closedComplement.base) (Set.range j.base) := by
    rw [j.range_closedComplement]
    exact disjoint_compl_left
  have (K : DerivedCategory (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq).app K) := by
    apply isIso_of_isIso_mapDerivedCategoryUpperStar_map _ j j.closedComplement
      j.range_closedComplement
    · exact isIso_upperStar_map_openImmersionLowerShriekLowerStarExchange_app Λ hsq K
    refine isIso_of_source_target_iso_zero _
      (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ j
        j.closedComplement hdisj _).isoZero (IsZero.isoZero ?_)
    let sq := IsPullback.of_hasPullback g'' j.closedComplement
    have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ hΛ sq
    let N := D((j')_!open[ModuleCat.{u + 1} Λ]).obj K
    have hN :
        IsZero (L((pullback.fst g'' j.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj N) := by
      refine IsZero.of_iso ?_ ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app N)
      refine isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _
        j' _ ?_ K
      rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
      have h₁ : g''.base ((pullback.fst g'' j.closedComplement).base x) ∈
          Set.range j.closedComplement.base := ⟨(pullback.snd g'' j.closedComplement).base x, by
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
      have h₂ : g''.base ((pullback.fst g'' j.closedComplement).base x) ∈ Set.range j.base :=
        ⟨g'.base y, by rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply, hy]⟩
      exact Set.disjoint_left.1 hdisj h₁ h₂
    exact IsZero.of_iso
      ((R((pullback.snd g'' j.closedComplement)_*[ModuleCat.{u + 1} Λ])).map_isZero hN)
      ((leftDerivedUpperStarIsoMapDerivedCategory _ _).symm.app _ ≪≫
        asIso ((derivedBaseChangeMap _ sq.toCommSq).app N))
  exact NatIso.isIso_of_isIso_app _

end Etale

end AlgebraicGeometry
