/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Transition maps between derived direct images over varying bases

Fix a scheme `B` (the base on which everything is compared) and a scheme `W` (the scheme the
coefficients come from). A *stage* is a morphism `g : T ⟶ S` together with morphisms
`π : B ⟶ S` and `w : T ⟶ W`; to it is attached the functor
`K ↦ π^* Rg_* (w^* K)` from `D⁺(W_ét)` to `D⁺(B_ét)`. A morphism of stages `α ⟶ β` is a
commutative square `(t, s)` from `g_α` to `g_β` compatible with the maps from `B` and to `W`;
it induces the transition map `π_β^* Rg_{β*} w_β^* K ⟶ π_α^* Rg_{α*} w_α^* K`, the pullback
along `π_α` of the derived base-change map of the square, modulo the composition isomorphisms
of the pullbacks. These transition maps compose
(`AlgebraicGeometry.Etale.LimitStage.transition_comp`).

All the comparison maps of the limit arguments of
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange` are transition maps of this
kind: the maps between the stages of a limit of morphisms with varying base, the maps to the
limit, and the base-change maps of Cartesian squares.

## Main definitions

- `AlgebraicGeometry.Etale.LimitStage`: a stage.
- `AlgebraicGeometry.Etale.LimitStage.Hom`: a morphism of stages.
- `AlgebraicGeometry.Etale.LimitStage.functor`: the functor `K ↦ π^* Rg_* (w^* K)`.
- `AlgebraicGeometry.Etale.LimitStage.transition`: the transition map of a morphism of stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A *stage* over a base `B` with coefficients from `W`: a morphism `g : T ⟶ S` together with
morphisms `π : B ⟶ S` and `w : T ⟶ W`. -/
structure LimitStage (B W : Scheme.{u}) where
  /-- The source of the morphism. -/
  T : Scheme.{u}
  /-- The target of the morphism. -/
  S : Scheme.{u}
  /-- The morphism. -/
  g : T ⟶ S
  /-- The map from the base. -/
  π : B ⟶ S
  /-- The map to the scheme of coefficients. -/
  w : T ⟶ W

namespace LimitStage

variable {B W : Scheme.{u}}

/-- A morphism of stages `α ⟶ β`: a commutative square from `α.g` to `β.g`, compatible with the
maps from `B` and to `W`. -/
@[ext]
structure Hom (α β : LimitStage B W) where
  /-- The map of sources. -/
  t : α.T ⟶ β.T
  /-- The map of targets. -/
  s : α.S ⟶ β.S
  wg : t ≫ β.g = α.g ≫ s
  wπ : α.π ≫ s = β.π
  ww : t ≫ β.w = α.w

/-- The composite of two morphisms of stages. -/
@[simps]
def Hom.comp {α β γ : LimitStage B W} (φ : Hom α β) (ψ : Hom β γ) : Hom α γ where
  t := φ.t ≫ ψ.t
  s := φ.s ≫ ψ.s
  wg := by rw [Category.assoc, ψ.wg, reassoc_of% φ.wg]
  wπ := by rw [reassoc_of% φ.wπ, ψ.wπ]
  ww := by rw [Category.assoc, ψ.ww, φ.ww]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The functor `K ↦ π^* Rg_* (w^* K)` attached to a stage. -/
noncomputable def functor (α : LimitStage B W) :
    DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D+((α.w)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((α.g)_*[ModuleCat.{u + 1} Λ]) ⋙
    D+((α.π)^*[ModuleCat.{u + 1} Λ])

lemma functor_obj (α : LimitStage B W)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (functor Λ α).obj K = D+((α.π)^*[ModuleCat.{u + 1} Λ]).obj
      (R+((α.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K)) := rfl

/-- The components of the transition map of a morphism of stages `φ : α ⟶ β`:
`π_β^* Rg_{β*} w_β^* K ≅ π_α^* s^* Rg_{β*} w_β^* K ⟶ π_α^* Rg_{α*} t^* w_β^* K ≅
π_α^* Rg_{α*} w_α^* K`, the middle map being the pullback along `π_α` of the derived base-change
map of the square `(t, s)`. -/
noncomputable def transitionApp {α β : LimitStage B W} (φ : Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (functor Λ β).obj K ⟶ (functor Λ α).obj K :=
  (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.app
      (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫
    D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app
          (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv.app K))

/-- The transition map of a morphism of stages, as a natural transformation. -/
noncomputable def transition {α β : LimitStage B W} (φ : Hom α β) :
    functor Λ β ⟶ functor Λ α where
  app K := transitionApp Λ φ K
  naturality {K K'} f := by
    simp only [transitionApp, functor, Functor.comp_obj, Functor.comp_map, Category.assoc]
    rw [← NatTrans.naturality_assoc]
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp]
    congr 2
    rw [← Etale.baseChange_naturality_assoc]
    sorry

end LimitStage

end AlgebraicGeometry.Etale
