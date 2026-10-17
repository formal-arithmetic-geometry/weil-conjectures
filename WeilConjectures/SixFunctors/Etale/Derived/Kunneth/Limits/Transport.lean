/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageAlgebra

/-!
# Change of the base of a system of stages, and maps of elementwise colimits

For `b : B' ⟶ B` and a stage `(T, S, g, π, w)` over `B`, the stage `(T, S, g, b ≫ π, w)` over `B'`
computes the pullback along `b` (`AlgebraicGeometry.Etale.LimitStage.comapBIso`), compatibly with
the transition maps; consequently stalkwise colimit systems are stable under change of base
(`AlgebraicGeometry.Etale.LimitStageSystem.isStalkColimit_comapB`).

A map of elementwise colimit systems which is bijective at every stage is bijective at the
colimit (`ModuleCat.IsElementwiseColimit.bijective_of_bijective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace ModuleCat.IsElementwiseColimit

variable {R : Type*} [Ring R] {I : Type*} [Category I]

/-- A map between two elementwise colimit systems over the same index category, compatible with
the structure maps and bijective at every stage, is bijective at the colimit. -/
lemma bijective_of_bijective {A A' : I → ModuleCat R} {B B' : ModuleCat R}
    {σ : ∀ i, A i ⟶ B} {σ' : ∀ i, A' i ⟶ B'} {τ : ∀ {i j : I}, (i ⟶ j) → (A j ⟶ A i)}
    {τ' : ∀ {i j : I}, (i ⟶ j) → (A' j ⟶ A' i)} (φ : ∀ i, A i ⟶ A' i) (φB : B ⟶ B')
    (hσ : ∀ i, φ i ≫ σ' i = σ i ≫ φB) (hτ : ∀ {i j : I} (f : i ⟶ j), τ f ≫ φ i = φ j ≫ τ' f)
    (hστ : ∀ {i j : I} (f : i ⟶ j), τ f ≫ σ i = σ j)
    (hφ : ∀ i, Function.Bijective (φ i).hom) (h : IsElementwiseColimit A B σ τ)
    (h' : IsElementwiseColimit A' B' σ' τ') : Function.Bijective φB.hom := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, fun b' ↦ ?_⟩
  · obtain ⟨i, a, rfl⟩ := h.1 b
    have h0 : (σ' i).hom ((φ i).hom a) = 0 := by rw [← ModuleCat.comp_apply, hσ]; exact hb
    obtain ⟨j, f, hf⟩ := h'.2 i _ h0
    have h1 : (φ j).hom ((τ f).hom a) = 0 := by rw [← ModuleCat.comp_apply, hτ]; exact hf
    have h2 : (τ f).hom a = 0 := (hφ j).1 (by rw [h1, map_zero])
    rw [← hστ f, ModuleCat.comp_apply, h2, map_zero]
  · obtain ⟨i, a', rfl⟩ := h'.1 b'
    obtain ⟨a, rfl⟩ := (hφ i).2 a'
    exact ⟨(σ i).hom a, by rw [← ModuleCat.comp_apply, ← hσ]; rfl⟩

end ModuleCat.IsElementwiseColimit

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace LimitStage

variable {B B' W : Scheme.{u}} (b : B' ⟶ B)

/-- Change of base: the stage `(T, S, g, b ≫ π, w)` over `B'`. -/
abbrev comapB (α : LimitStage B W) : LimitStage B' W := ⟨α.T, α.S, α.g, b ≫ α.π, α.w⟩

/-- Change of base for morphisms of stages. -/
abbrev Hom.comapB {α β : LimitStage B W} (φ : Hom α β) : Hom (α.comapB b) (β.comapB b) :=
  ⟨φ.t, φ.s, φ.wg, by rw [Category.assoc, φ.wπ], φ.ww⟩

/-- `b^* π^* Rg_* w^* K ≅ (b ≫ π)^* Rg_* w^* K`. -/
noncomputable def comapBIso (α : LimitStage B W)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((b)^*[ModuleCat.{u + 1} Λ]).obj ((functor Λ α).obj K) ≅ (functor Λ (α.comapB b)).obj K :=
  ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b α.π (b ≫ α.π) rfl).app
    (R+((α.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K))).symm

lemma transition_comapB {α β : LimitStage B W} (φ : Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((b)^*[ModuleCat.{u + 1} Λ]).map ((transition Λ φ).app K) ≫ (comapBIso Λ b α K).hom =
      (comapBIso Λ b β K).hom ≫ (transition Λ (φ.comapB b)).app K := by
  have hA := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    b α.π φ.s (b ≫ α.π) β.π (b ≫ β.π) rfl φ.wπ.symm (by rw [Category.assoc, φ.wπ]))
    (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hA
  have hA' : D+((b)^*[ModuleCat.{u + 1} Λ]).map
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.app
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K))) ≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b α.π (b ≫ α.π) rfl).inv.app
        (D+((φ.s)^*[ModuleCat.{u + 1} Λ]).obj
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K))) =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b β.π (b ≫ β.π) rfl).inv.app
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (b ≫ α.π) φ.s (b ≫ β.π)
          (φ.comapB b).wπ.symm).hom.app
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [← cancel_epi ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b β.π (b ≫ β.π)
      rfl).hom.app _), Iso.hom_inv_id_app_assoc, reassoc_of% hA, Iso.hom_inv_id_app,
      Category.comp_id]
  have n := (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b α.π (b ≫ α.π) rfl).inv.naturality
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv.app K))
  simp only [Functor.comp_map] at n
  simp only [transition_app, comapBIso, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [n, reassoc_of% hA']

end LimitStage

namespace LimitStageSystem

variable {B B' W : Scheme.{u}} {I : Type u} [Category.{u} I] (b : B' ⟶ B)

/-- Change of base of a system of stages along `b : B' ⟶ B`. -/
@[simps]
def comapB (𝒮 : LimitStageSystem B W I) : LimitStageSystem B' W I where
  obj i := (𝒮.obj i).comapB b
  map f := (𝒮.map f).comapB b
  map_id i := LimitStage.Hom.ext (by rw [𝒮.map_id]) (by rw [𝒮.map_id])
  map_comp f g := LimitStage.Hom.ext (by rw [𝒮.map_comp]) (by rw [𝒮.map_comp])
  pt := 𝒮.pt.comapB b
  π i := (𝒮.π i).comapB b
  w f := LimitStage.Hom.ext (by rw [← 𝒮.w f]) (by rw [← 𝒮.w f])

variable {Λ}

/-- Stalkwise colimit systems are stable under change of base. -/
lemma isStalkColimit_comapB [IsCofiltered I] (𝒮 : LimitStageSystem B W I)
    {K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {q : ℤ}
    (h : 𝒮.IsStalkColimit Λ K q) : (𝒮.comapB b).IsStalkColimit Λ K q := by
  have hcol := isColimitOfPreserves ((b)^*[ModuleCat.{u + 1} Λ]) (𝒮.isColimitOfIsStalkColimit Λ h)
  intro x
  let e (α : LimitStage B W) := (((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      q).app ((LimitStage.functor Λ α).obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso (LimitStage.comapBIso Λ b α K)
  have he {α β : LimitStage B W} (φ : LimitStage.Hom α β) :
      ((b)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ φ).app K)) ≫ (e α).hom =
      (e β).hom ≫ (DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ (φ.comapB b)).app K) := by
    have n := (((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).hom.naturality
      ((LimitStage.transition Λ φ).app K)
    simp only [Functor.comp_map] at n
    simp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, reassoc_of% n,
      ← Functor.map_comp, LimitStage.transition_comapB]
  have he' {α β : LimitStage B W} (φ : LimitStage.Hom α β) :
      (e β).inv ≫ ((b)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ φ).app K)) =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ (φ.comapB b)).app K) ≫ (e α).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ModuleCat.IsElementwiseColimit.of_iso
    (fun i ↦ ((B'.uliftPointSmallEtale x).sheafFiber.mapIso (e (𝒮.obj i))).symm)
    ((B'.uliftPointSmallEtale x).sheafFiber.mapIso (e 𝒮.pt)).symm (fun i ↦ ?_) (fun f ↦ ?_)
    (isElementwiseColimit_sheafFiber_of_isColimit hcol x)
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Functor.mapCocone_ι_app, cocone_ι_app,
      Quiver.Hom.unop_op, stalkHomology, Functor.comp_map, ← Functor.map_comp]
    exact congrArg (B'.uliftPointSmallEtale x).sheafFiber.map (he' (𝒮.π i))
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Functor.comp_map, diagram_map,
      Quiver.Hom.unop_op, stalkHomology, ← Functor.map_comp]
    exact congrArg (B'.uliftPointSmallEtale x).sheafFiber.map (he' (𝒮.map f))

end LimitStageSystem

end AlgebraicGeometry.Etale
