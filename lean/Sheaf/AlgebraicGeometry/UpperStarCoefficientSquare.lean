/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.BaseChange.Pasting

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


private lemma comparison_inv_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z) (w : f ≫ g = r)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarComp (ModuleCat.{u + 1} Λ) f g).inv.app F ≫
      eqToHom (congrArg (fun k ↦ ((k)^*[ModuleCat.{u + 1} Λ]).obj F) w) =
    (upperStarComp (ModuleCat.{u + 1} Λ) f g r w.symm).inv.app F := by
  subst r
  simp only [eqToHom_refl, Category.comp_id]

private lemma comparison_assoc_inv {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((f)^*[ModuleCat.{u + 1} Λ]).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) g h gh hgh).inv.app F) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) f gh fgh
        (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app F =
    (upperStarComp (ModuleCat.{u + 1} Λ) f g fg hfg).inv.app
        (((h)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
      (upperStarComp (ModuleCat.{u + 1} Λ) fg h fgh hfgh).inv.app F := by
  apply (cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) f g fg hfg).hom.app
    (((h)^*[ModuleCat.{u + 1} Λ]).obj F))).mp
  rw [upperStarComp_hom_app_map_upperStarComp_inv_app_assoc
    (ModuleCat.{u + 1} Λ) f g h fg gh fgh hfg hgh hfgh F]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]


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
          (((j)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  let A := ModuleCat.{u + 1} Λ
  have ht : fU ≫ u = a ≫ (fV ≫ v) := by
    rw [← Category.assoc, wf, Category.assoc, wu]
  have hr : kU ≫ j = (cU ≫ a) ≫ (fV ≫ v) := by
    rw [Category.assoc, ← ht, wU]
  have hd :
      (upperStarComp A a fV).inv.app (((v)^*[A]).obj F) ≫
        (upperStarComp A fU φ (a ≫ fV) wf).hom.app (((v)^*[A]).obj F) ≫
        ((fU)^*[A]).map ((upperStarComp A φ v u wu.symm).inv.app F) ≫
        (upperStarComp A fU u).inv.app F =
      ((a)^*[A]).map ((upperStarComp A fV v).inv.app F) ≫
        (upperStarComp A a (fV ≫ v) (fU ≫ u) ht).inv.app F := by
    have h1 := comparison_assoc_inv Λ fU φ v (a ≫ fV) u (fU ≫ u)
      wf wu.symm (by rw [wf, Category.assoc, wu]) F
    have h2 := comparison_assoc_inv Λ a fV v (a ≫ fV) (fV ≫ v) (fU ≫ u)
      rfl rfl (by rw [Category.assoc, ← ht]) F
    rw [h1, Iso.hom_inv_id_app_assoc]
    exact h2.symm
  have hU := comparison_assoc_inv Λ cU a (fV ≫ v) (cU ≫ a) (fU ≫ u) (kU ≫ j)
    rfl ht hr F
  have hV := comparison_assoc_inv Λ b cV (fV ≫ v) (cU ≫ a) (kV ≫ j) (kU ≫ j)
    ws wV.symm hr F
  have hK := map_upperStarComp_hom_app_upperStarComp_inv_app A b kV j kU
    (kV ≫ j) (kU ≫ j) wk.symm rfl rfl F
  have hnU := (upperStarComp A cU a).hom.naturality
    ((upperStarComp A fV v).inv.app F)
  have hnV := (upperStarComp A b cV (cU ≫ a) ws).hom.naturality
    ((upperStarComp A fV v).inv.app F)
  dsimp only [A] at hd hK hnU hnV
  dsimp only
  rw [reassoc_of% comparison_inv_transport Λ cU (fU ≫ u) (kU ≫ j) wU F,
    reassoc_of% comparison_inv_transport Λ cV (fV ≫ v) (kV ≫ j) wV F]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hd, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hU, ← reassoc_of% hnU]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [hK, reassoc_of% hV, ← reassoc_of% hnV]
  simp only [Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Etale
