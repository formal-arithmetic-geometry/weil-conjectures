/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Underived coefficient coherence for two presentations

Source: Stacks Project Tags 0F07 and 09Z1, coefficient identification.
(blueprint: lem-sbc-upper-star-coefficient-square)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Coefficient restriction commutes with changing a two-step presentation of pullback.

Source: Stacks Project Tag 0F07, coefficient identification preceding condition (2),
and Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-upper-star-coefficient-square)

Proof: Replace each two-step coefficient pullback by the single pullback along the
composite, using upperStarComp. Naturality moves a mapped comparison past the next
composition comparison. Apply upperStarComp_assoc to the triples (cU,a,fV),
(cU,fU,φ), (fU,φ,v), (b,cV,fV), (cV,fV,v), and (b,kV,j).
The inverse and forward comparisons at the intermediate paths cancel. Transport
along wf, wu, wV, wU and wk identifies the composites. The equality ws identifies
the two paths ZU→YV, so the uncancelled comparisons on both sides are the same
map from (cU≫a)^*(fV^*v^*F) to kU^*j^*F. Proof irrelevance removes dependence
on the witnesses of these arrow equalities. This is underived functor coherence:
it holds also for identity arrows, zero sheaves and arbitrary commutative rings. -/
theorem upperStar_coefficient_square
    {T U V W YV YU ZV ZU : Scheme.{u}}
    (v : V ⟶ T) (u : U ⟶ T) (φ : U ⟶ V) (wu : φ ≫ v = u)
    (fV : YV ⟶ V) (fU : YU ⟶ U) (a : YU ⟶ YV) (wf : a ≫ fV = fU ≫ φ)
    (j : W ⟶ T) (kV : ZV ⟶ W) (kU : ZU ⟶ W)
    (cV : ZV ⟶ YV) (cU : ZU ⟶ YU) (b : ZU ⟶ ZV)
    (wV : cV ≫ (fV ≫ v) = kV ≫ j) (wU : cU ≫ (fU ≫ u) = kU ≫ j)
    (wk : b ≫ kV = kU) (ws : cU ≫ a = b ≫ cV)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let FV := ((fV)^*[ModuleCat.{u + 1} Λ]).obj (((v)^*[ModuleCat.{u + 1} Λ]).obj F)
    let d := (upperStarComp (ModuleCat.{u + 1} Λ) a fV).inv.app
        (((v)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) fU φ (a ≫ fV) wf).hom.app
        (((v)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
      ((fU)^*[ModuleCat.{u + 1} Λ]).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) φ v u wu.symm).inv.app F)
    let eV := ((cV)^*[ModuleCat.{u + 1} Λ]).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) fV v).inv.app F) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) cV (fV ≫ v)).inv.app F ≫
      eqToHom (congrArg (fun k ↦ ((k)^*[ModuleCat.{u + 1} Λ]).obj F) wV) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) kV j).hom.app F
    let eU := ((cU)^*[ModuleCat.{u + 1} Λ]).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) fU u).inv.app F) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) cU (fU ≫ u)).inv.app F ≫
      eqToHom (congrArg (fun k ↦ ((k)^*[ModuleCat.{u + 1} Λ]).obj F) wU) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) kU j).hom.app F
    (upperStarComp (ModuleCat.{u + 1} Λ) cU a).hom.app FV ≫
        ((cU)^*[ModuleCat.{u + 1} Λ]).map d ≫ eU =
      (upperStarComp (ModuleCat.{u + 1} Λ) b cV (cU ≫ a) ws).hom.app FV ≫
        ((b)^*[ModuleCat.{u + 1} Λ]).map eV ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) b kV kU wk.symm).inv.app
          (((j)^*[ModuleCat.{u + 1} Λ]).obj F) := by sorry

end AlgebraicGeometry.Etale
