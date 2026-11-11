/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperShriekCompCompForgetSupports
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar

/-!
# Forgetting supports and composition

For finite coefficients `Λ` and a morphism `f : X ⟶ Y` admitting a compactification, the
forget-supports map `η_f : Rf_! ⟶ Rf_*` of the chosen compactification `f = p ∘ j` is
`Rp_* j_! ⟶ Rp_* Rj_* = Rf_*` (`AlgebraicGeometry.Etale.compactificationForgetSupports`). It
does not depend on the compactification
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar`),
and it is compatible with the composition isomorphisms `c^!_{g,f} : Rg_! Rf_! ≅ R(gf)_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`) and
`c^*_{g,f} : Rg_* Rf_* ≅ R(gf)_*` (`AlgebraicGeometry.Etale.rightDerivedLowerStarCompIsoOfComp`):
```
Rg_! Rf_! ──c^!_{g,f}──▶ R(gf)_!
    │                       │
Rg_*(η_f) ∘ (η_g Rf_!)    η_{gf}
    ▼                       ▼
Rg_* Rf_* ──c^*_{g,f}──▶ R(gf)_*
```
This is blueprint `proposition-forgetting-supports-composition--2`.

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso_inv_app_comp_forgetSupports`: the
  square.
- `AlgebraicGeometry.Etale.forgetSupports_independent_and_comp`: the clause, independence and
  the square.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}}

/-- **Forgetting supports is compatible with composition**: for composable `f : X ⟶ Y` and
`g : Y ⟶ S`, the square
```
Rg_! Rf_! ──c^!_{g,f}──▶ R(gf)_!
    │                       │
Rg_*(η_f) ∘ (η_g Rf_!)    η_{gf}
    ▼                       ▼
Rg_* Rf_* ──c^*_{g,f}──▶ R(gf)_*
```
commutes, where `η` are the forget-supports maps of the chosen compactifications,
`c^!_{g,f}` is the composition isomorphism of the compactly supported direct images and
`c^*_{g,f}` that of the ordinary direct images. -/
theorem rightDerivedLowerShriekCompIso_inv_app_comp_forgetSupports (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] (K : DerivedCategoryModule Λ X) :
    (rightDerivedLowerShriekCompIso Λ f g).inv.app K ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification (f ≫ g))).app K =
      (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification g)).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.map
          ((compactificationForgetSupports (ModuleCat.{u + 1} Λ)
            (HasCompactification.compactification f)).app K) ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) f g (f ≫ g) rfl).hom.app K := by
  have : QuasiCompact f := .of_comp f g
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  have hcomp := rightDerivedLowerShriekOfCompactificationCompIso_hom_app_comp_forgetSupports
    Λ f g d e K
  have hα : (rightDerivedLowerShriekIso Λ (d.comp e)).hom.app K ≫
      (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification (f ≫ g))).app K =
      (compactificationForgetSupports (ModuleCat.{u + 1} Λ) (d.comp e)).app K :=
    rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar Λ
      (d.comp e) (HasCompactification.compactification (f ≫ g)) K
  have hβ' : (rightDerivedLowerShriekIso Λ e.restrict).hom.app K ≫
      (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification f)).app K =
      (compactificationForgetSupports (ModuleCat.{u + 1} Λ) e.restrict).app K :=
    rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar Λ e.restrict
      (HasCompactification.compactification f) K
  have hβ : (rightDerivedLowerShriekIso Λ e.restrict).inv.app K ≫
      (compactificationForgetSupports (ModuleCat.{u + 1} Λ) e.restrict).app K =
      (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification f)).app K := by
    rw [← hβ']
    exact Iso.inv_hom_id_app_assoc _ _ _
  have hn := (compactificationForgetSupports (ModuleCat.{u + 1} Λ) d).naturality
    ((compactificationForgetSupports (ModuleCat.{u + 1} Λ)
      (HasCompactification.compactification f)).app K)
  simp only [rightDerivedLowerShriekCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
  rw [hα, hcomp, ← Functor.map_comp_assoc, hβ]
  exact (reassoc_of% hn) _

/-- Blueprint `proposition-forgetting-supports-composition--2`: the forget-supports map
`η_f : Rf_! ⟶ Rf_*` **is independent of the compactification** (for two compactifications `c`,
`d` of `f`, the comparison `Rf_!(c) ≅ Rf_!(d)` followed by `η` of `d` is `η` of `c`), and **the
square**
```
Rg_! Rf_! ──c^!_{g,f}──▶ R(gf)_!
    │                       │
Rg_*(η_f) ∘ (η_g Rf_!)    η_{gf}
    ▼                       ▼
Rg_* Rf_* ──c^*_{g,f}──▶ R(gf)_*
```
**commutes** (`rightDerivedLowerShriekCompIso_inv_app_comp_forgetSupports`), where `c^!_{g,f}`
is the composition isomorphism of `R(-)_!` (`rightDerivedLowerShriekCompIso`) and `c^*_{g,f}` the
composition isomorphism of the ordinary direct images (`rightDerivedLowerStarCompIsoOfComp`). -/
theorem forgetSupports_independent_and_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    (∀ (c d : Compactification f) (M : DerivedCategoryModule Λ X),
      (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom.app M ≫
          (compactificationForgetSupports (ModuleCat.{u + 1} Λ) d).app M =
        (compactificationForgetSupports (ModuleCat.{u + 1} Λ) c).app M) ∧
    ∀ K : DerivedCategoryModule Λ X,
      (rightDerivedLowerShriekCompIso Λ f g).inv.app K ≫
          (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
            (HasCompactification.compactification (f ≫ g))).app K =
        (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
            (HasCompactification.compactification g)).app
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.map
            ((compactificationForgetSupports (ModuleCat.{u + 1} Λ)
              (HasCompactification.compactification f)).app K) ≫
          (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) f g (f ≫ g) rfl).hom.app K :=
  ⟨fun c d M ↦ rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar Λ c d M,
    rightDerivedLowerShriekCompIso_inv_app_comp_forgetSupports Λ f g⟩

end Etale

end AlgebraicGeometry
