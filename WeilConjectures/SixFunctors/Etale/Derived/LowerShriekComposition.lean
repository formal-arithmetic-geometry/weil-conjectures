/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Comp
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

/-!
# The composition law for `Rf_!`

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes admitting compactifications, with
`f ≫ g` quasi-compact. This file constructs, for torsion coefficients, the composition
isomorphism

`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`

of the compactly supported direct images on the unbounded derived categories of étale sheaves
(blueprint `sk-thm-sf-comp-composition`, `thm-sf-comp-composition`).

Following the blueprint, compactify `g` as `Y ⟶[v] Ȳ ⟶[ḡ] S` and `f ≫ v` as
`X ⟶[a] X̄ ⟶[p] Ȳ`. Then `V = X̄ ×_Ȳ Y` with its open immersion `b : V ⟶ X̄` and proper
projection `p_Y : V ⟶ Y` gives the compactification `X ⟶[c] V ⟶[p_Y] Y` of `f`
(`AlgebraicGeometry.Compactification.restrict`), and `X ⟶[a] X̄ ⟶[p ≫ ḡ] S` is a
compactification of `f ≫ g` (`AlgebraicGeometry.Compactification.comp`). On these models

```
Rf_! ⋙ Rg_! = Dc_! ⋙ Rp_Y* ⋙ Dv_! ⋙ Rḡ_*
           ≅ Dc_! ⋙ Db_! ⋙ Rp_* ⋙ Rḡ_*        (v_! Rp_Y* ≅ Rp_* b_!)
           ≅ Da_! ⋙ R(p ≫ ḡ)_* = R(f ≫ g)_!
```

where the middle isomorphism is the exchange of an extension by zero with a proper
pushforward,
`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`,
which rests on proper base change. The comparison with the chosen compactifications of `f`
and `f ≫ g` is the independence of the compactification,
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`.

## Main definitions

- `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekComp`: the composition
  isomorphism `D((j' ≫ j)_!) ≅ D(j'_!) ⋙ D(j_!)` of derived extensions by zero.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso`: the isomorphism
  `Rf_!(e.restrict) ⋙ Rg_!(d) ≅ R(f ≫ g)_!(d.comp e)` on the models above.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`: the composition law
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
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

section OpenImmersion

variable {V U X : Scheme.{u}}

/-- The composition isomorphism `D((j' ≫ j)_!) ≅ D(j'_!) ⋙ D(j_!)` of the extensions by zero
along open immersions `j' : V ⟶ U` and `j : U ⟶ X`, on unbounded derived categories, induced by
`AlgebraicGeometry.Etale.openImmersionLowerShriekComp`. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekComp (j' : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion j'] [IsOpenImmersion j] :
    D((j' ≫ j)_!open[A]) ≅ D((j')_!open[A]) ⋙ D((j)_!open[A]) :=
  Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekComp A j' j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The isomorphism `D(j_!) ≅ D(j'_!)` of derived extensions by zero induced by an equality
`j = j'` of open immersions. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekCongr {j j' : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j') :
    D((j)_!open[A]) ≅ D((j')_!open[A]) := by
  subst h
  exact Iso.refl _

end OpenImmersion

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} {f : X ⟶ Y}
  {g : Y ⟶ S}

/-- **The composition isomorphism on compatible compactifications.** Let `d = (v, ḡ)` be a
compactification of `g : Y ⟶ S` and `e = (a, p)` a compactification of `f ≫ v`, and write
`V = e.Z ×_{d.Z} Y` with its open immersion `b : V ⟶ e.Z` and its proper projection
`p_Y : V ⟶ Y`. For torsion coefficients, the isomorphism

```
Rf_!(e.restrict) ⋙ Rg_!(d) = Dc_! ⋙ Rp_Y* ⋙ Dv_! ⋙ Rḡ_*
    ≅ Dc_! ⋙ Db_! ⋙ Rp_* ⋙ Rḡ_*  ≅  Da_! ⋙ R(p ≫ ḡ)_* = R(f ≫ g)_!(d.comp e)
```

built from the exchange isomorphism `v_! Rp_Y* ≅ Rp_* b_!` of the cartesian square
`AlgebraicGeometry.Compactification.isPullback_restrict` (an isomorphism by proper base
change), the composition of extensions by zero along `a = c ≫ b`, and the composition of
derived pushforwards. (blueprint: the construction in `sk-thm-sf-comp-composition`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationCompIso (d : Compactification g)
    (e : Compactification (f ≫ d.i)) :
    Rf_!(e.restrict)[ModuleCat.{u + 1} Λ] ⋙ Rf_!(d)[ModuleCat.{u + 1} Λ] ≅
      Rf_!(d.comp e)[ModuleCat.{u + 1} Λ] :=
  have := isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite e.isPullback_restrict
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D((e.restrict.i)_!open[ModuleCat.{u + 1} Λ])
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso (openImmersionLowerShriekLowerStarExchange _
          e.isPullback_restrict)) R((d.g)_*[ModuleCat.{u + 1} Λ]) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D((pullback.fst e.g d.i)_!open[ModuleCat.{u + 1} Λ])
          (rightDerivedLowerStarComp _ e.g d.g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((mapDerivedCategoryOpenImmersionLowerShriekComp _ e.restrict.i
          (pullback.fst e.g d.i)).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr _ e.restrict_i_fst)
      R((e.g ≫ d.g)_*[ModuleCat.{u + 1} Λ])

/-- Blueprint `sk-thm-sf-comp-composition` (detailed: `thm-sf-comp-composition`): **the
composition law for `Rf_!`**. For composable `f : X ⟶ Y` and `g : Y ⟶ S` admitting
compactifications, with `f ≫ g` quasi-compact, and torsion coefficients, there is an
isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of functors between the unbounded derived categories of
étale sheaves.

It is `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso` for the chosen
compactification `d` of `g` and the compactification
`AlgebraicGeometry.Compactification.ofComp` of `f ≫ d.i`, compared with the chosen
compactifications of `f` and `f ≫ g` by `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`.
The quasi-compactness of `f ≫ g` (automatic for the finite-type morphisms of the blueprint) is
what makes the compactly supported direct image independent of the compactification. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    Nonempty (R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]) := by
  have : QuasiCompact f := .of_comp f g
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  exact ⟨(rightDerivedLowerShriekIso Λ (d.comp e)).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ d e).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ e.restrict) _⟩

end Torsion

end Etale

end AlgebraicGeometry
