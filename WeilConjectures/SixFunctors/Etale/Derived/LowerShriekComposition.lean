/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Comp
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
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


section Plus

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S T : Scheme.{u}}

/-- The comparison isomorphism `Rf_!(c)[Λ]+ ≅ Rf_!(d)[Λ]+` between the bounded below compactly
supported direct images attached to two compactifications of a quasi-compact morphism: the one of
the compact support formalism `AlgebraicGeometry.Etale.derivedPlusFormalism`, obtained through
the common refinement `Compactification.inf c d` and satisfying the coherences of blueprint
`sk-prop-sf-comp-coherence` (`CompactSupportFormalism.shriekIso_eq`,
`CompactSupportFormalism.shriekIso_trans`). -/
noncomputable abbrev rightDerivedLowerShriekPlusCompactificationIso {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ]+ ≅ Rf_!(d)[ModuleCat.{u + 1} Λ]+ :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso c d

/-- The isomorphism `R(f)_![Λ]+ ≅ R(f')_![Λ]+` for `f = f'`. -/
noncomputable abbrev rightDerivedLowerShriekPlusCongr {f f' : X ⟶ Y} [HasCompactification f]
    [HasCompactification f'] (h : f = f') :
    R(f)_![ModuleCat.{u + 1} Λ]+ ≅ R(f')_![ModuleCat.{u + 1} Λ]+ :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCongr h

/-- The identification `R(𝟙 X)_![Λ]+ ≅ 𝟭` of the bounded below compactly supported direct image
along the identity. -/
noncomputable abbrev rightDerivedLowerShriekPlusId (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    R(𝟙 X)_![ModuleCat.{u + 1} Λ]+ ≅ 𝟭 _ :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekId X

/-- Blueprint `sk-thm-sf-comp-composition` (detailed: `thm-sf-comp-composition`): **the canonical
composition isomorphism** `α_{g,f} : Rg_! Rf_! ≅ R(g ∘ f)_!` of functors `D⁺(X_ét, Λ) ⥤ D⁺(S_ét, Λ)`
for torsion coefficients, for composable `f`, `g` admitting compactifications with `f ≫ g`
quasi-compact. It is the composition isomorphism `CompactSupportFormalism.compIso` of the
triangle of compactifications `Compactification.Triangle.ofHasCompactification f g`: compactify
`g` as `Y ⟶[v] Ȳ ⟶[ḡ] S` and `f ≫ v` as `X ⟶[a] X̄ ⟶[p] Ȳ`; with `V = X̄ ×_Ȳ Y`, the exchange
isomorphism `v_! Rp_{Y*} ≅ Rp_* b_!` (proper base change) gives
`Rf_! ⋙ Rg_! = c_! Rp_{Y*} v_! Rḡ_* ≅ a_! R(p ≫ ḡ)_* = R(f ≫ g)_!`, compared with the chosen
compactifications of `f` and `f ≫ g`. -/
noncomputable def rightDerivedLowerShriekPlusCompIso (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    R(f)_![ModuleCat.{u + 1} Λ]+ ⋙ R(g)_![ModuleCat.{u + 1} Λ]+ ≅
      R(f ≫ g)_![ModuleCat.{u + 1} Λ]+ :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso f g

/-- Blueprint `sk-thm-sf-comp-composition`: **independence of all compactification choices**. The
composition isomorphism is computed by any triangle of compactifications `T` of `(f, g)`
(compactifications of `f`, `g`, `f ≫ g` linked by a cartesian square): it is the composition
isomorphism of `T`, conjugated by the comparison isomorphisms between the compactifications of
`T` and the chosen ones. -/
theorem rightDerivedLowerShriekPlusCompIso_hom_eq {f : X ⟶ Y} {g : Y ⟶ S}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] (T : Compactification.Triangle f g) :
    (rightDerivedLowerShriekPlusCompIso Λ f g).hom =
      NatTrans.hcomp
          (rightDerivedLowerShriekPlusCompactificationIso Λ
            (HasCompactification.compactification f) T.cf).hom
          (rightDerivedLowerShriekPlusCompactificationIso Λ
            (HasCompactification.compactification g) T.cg).hom ≫
        ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).compIso T).hom ≫
          (rightDerivedLowerShriekPlusCompactificationIso Λ T.cfg
            (HasCompactification.compactification (f ≫ g))).hom :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_hom_eq T

/-- Blueprint `sk-thm-sf-comp-composition`: **the composition isomorphism is the identity when
`f` is an identity**. -/
theorem rightDerivedLowerShriekPlusCompIso_id_left (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (𝟙 X)] [HasCompactification (𝟙 X ≫ f)] [QuasiCompact f] :
    (rightDerivedLowerShriekPlusCompIso Λ (𝟙 X) f).hom =
      Functor.whiskerRight (rightDerivedLowerShriekPlusId Λ X).hom _ ≫
        (Functor.leftUnitor _).hom ≫
          (rightDerivedLowerShriekPlusCongr Λ (Category.id_comp f).symm).hom :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_id_left f

/-- Blueprint `sk-thm-sf-comp-composition`: **the composition isomorphism is the identity when
`g` is an identity**. -/
theorem rightDerivedLowerShriekPlusCompIso_id_right (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (𝟙 Y)] [HasCompactification (f ≫ 𝟙 Y)] [QuasiCompact f] :
    (rightDerivedLowerShriekPlusCompIso Λ f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (rightDerivedLowerShriekPlusId Λ Y).hom ≫
        (Functor.rightUnitor _).hom ≫
          (rightDerivedLowerShriekPlusCongr Λ (Category.comp_id f).symm).hom :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_id_right f

/-- Blueprint `sk-thm-sf-comp-composition`: **associativity of the composition isomorphism**: for
a third morphism `h : S ⟶ T`, the two composites `Rh_! Rg_! Rf_! ≅ R(f ≫ g ≫ h)_!` agree. -/
theorem rightDerivedLowerShriekPlusCompIso_assoc (f : X ⟶ Y) (g : Y ⟶ S) (h : S ⟶ T)
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] [QuasiCompact f]
    [QuasiCompact g] [QuasiCompact h] :
    Functor.whiskerRight (rightDerivedLowerShriekPlusCompIso Λ f g).hom
        R(h)_![ModuleCat.{u + 1} Λ]+ ≫ (rightDerivedLowerShriekPlusCompIso Λ (f ≫ g) h).hom ≫
        (rightDerivedLowerShriekPlusCongr Λ (Category.assoc f g h)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R(f)_![ModuleCat.{u + 1} Λ]+
          (rightDerivedLowerShriekPlusCompIso Λ g h).hom ≫
          (rightDerivedLowerShriekPlusCompIso Λ f (g ≫ h)).hom :=
  (derivedPlusFormalism (ModuleCat.{u + 1} Λ)).lowerShriekCompIso_assoc f g h

end Plus

end Etale

end AlgebraicGeometry
