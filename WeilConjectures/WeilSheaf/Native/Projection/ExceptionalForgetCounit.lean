/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointForget
public import WeilConjectures.WeilSheaf.Native.Projection.UniversalArrowMate

/-! # The counit normalization of the derived exceptional Weil lift -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

/-- The construction of the exceptional Weil lift, retaining the equation identifying its
underlying counit with the geometric counit. -/
theorem exists_bijective_rightDerivedFunctor_map_comp_free_with_forget
    (PC : ObjectProperty (DerivedCategory C))
    (PD : ObjectProperty (DerivedCategory D)) [PC.IsClosedUnderIsomorphisms]
    (hPC : ∀ K, PC K → DerivedCategory.TStructure.t.bounded K)
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    {R' : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⊣ R')
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    (L' : DerivedCategory (IsoAlgebra G)) (hL' : PD ((forget G).mapDerivedCategory.obj L')) :
    ∃ (H : DerivedCategory (IsoAlgebra F)) (_ : PC ((forget F).mapDerivedCategory.obj H))
      (eH : (forget F).mapDerivedCategory.obj H ≅ (R'.obj ⟨_, hL'⟩).obj)
      (d : (mapOfNatIso e).rightDerivedFunctor.obj H ⟶ L'),
      (forget G).mapDerivedCategory.map d =
        (derivedForgetCommIso e).hom.app H ≫ L.rightDerivedFunctor.map eH.hom ≫
          (adj.counit.app ⟨_, hL'⟩).hom ∧
      ∀ X, PC X → Function.Bijective
        (fun u : (Free.functor F).mapDerivedCategory.obj X ⟶ H ↦
          (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) := by
  let RL := L.rightDerivedFunctor
  let Y : PD.FullSubcategory := ⟨_, hL'⟩
  let N := (R'.obj Y).obj
  have hN : PC N := (R'.obj Y).property
  let ε : RL.obj N ⟶ (forget G).mapDerivedCategory.obj L' := (adj.counit.app Y).hom
  obtain ⟨v, hv⟩ := exists_iso_counit_isWeilEquivariant e PC PD hR adj hPC_F hPD_G Y
    ((derivedStrIso G).app L')
  obtain ⟨H, eH, hσ, -, -⟩ := exists_cyclicDerivedActionRealization F N (hPC N hN) v
  have hσ' : (derivedStrIso F).hom.app H ≫ eH.hom = F.mapDerivedCategory.map eH.hom ≫ v.hom :=
    hσ
  have hH : PC ((forget F).mapDerivedCategory.obj H) := PC.prop_of_iso eH.symm hN
  let c := (derivedForgetCommIso e).hom.app H ≫ RL.map eH.hom ≫ ε
  have hc : (derivedStrIso G).hom.app ((mapOfNatIso e).rightDerivedFunctor.obj H) ≫ c =
      G.mapDerivedCategory.map c ≫ (derivedStrIso G).hom.app L' := by
    have hχ := (derivedCommIso e).hom.naturality eH.hom
    dsimp at hχ
    have hv' : (derivedCommIso e).hom.app N ≫ RL.map v.hom ≫ ε =
        G.mapDerivedCategory.map ε ≫ (derivedStrIso G).hom.app L' := hv
    simp only [c, Functor.map_comp, Category.assoc]
    rw [reassoc_of% (derivedStrIso_hom_app_comp_derivedForgetCommIso e H),
      ← Functor.map_comp_assoc, hσ', Functor.map_comp, Category.assoc, ← reassoc_of% hχ, hv']
  obtain ⟨d, hd⟩ := exists_forget_mapDerivedCategory_map_eq G c hc
  refine ⟨H, hH, eH, d, hd, fun X hX ↦ ?_⟩
  obtain ⟨a, ha⟩ := (hPC X hX).1
  have : X.IsGE a := ha
  have : IsIso (derivedFreeComparison e X) := isIso_derivedFreeComparison e hcoprod X a
  let adjF := freeWeilDerivedAdjunction F
  let adjG := freeWeilDerivedAdjunction G
  have key (u : (Free.functor F).mapDerivedCategory.obj X ⟶ H) :
      (mapOfNatIso e).rightDerivedFunctor.map u ≫ d = inv (derivedFreeComparison e X) ≫
        (adjG.homEquiv _ _).symm (RL.map (adjF.homEquiv _ _ u ≫ eH.hom) ≫ ε) := by
    rw [IsIso.eq_inv_comp]
    apply (adjG.homEquiv _ _).injective
    have hβ := (derivedForgetCommIso e).inv.naturality u
    dsimp at hβ
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, hd,
      unit_app_comp_map_derivedFreeComparison_assoc, Adjunction.homEquiv_unit, ← reassoc_of% hβ]
    simp only [c, Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
    rfl
  have hfun : (fun u : (Free.functor F).mapDerivedCategory.obj X ⟶ H ↦
      (mapOfNatIso e).rightDerivedFunctor.map u ≫ d) =
      (fun y ↦ inv (derivedFreeComparison e X) ≫ y) ∘ (adjG.homEquiv _ _).symm ∘
        (fun w ↦ RL.map w ≫ ε) ∘ (fun w ↦ w ≫ eH.hom) ∘ (adjF.homEquiv _ _) :=
    funext key
  rw [hfun]
  refine Function.Bijective.comp ?_ ((Equiv.bijective _).comp
    ((bijective_map_comp_counit_app_hom PC PD RL hR adj Y X hX).comp
      (Function.Bijective.comp ?_ (Equiv.bijective _))))
  · exact ⟨fun y y' h ↦ (cancel_epi _).1 h, fun y ↦ ⟨derivedFreeComparison e X ≫ y, by simp⟩⟩
  · exact ⟨fun w w' h ↦ (cancel_mono eH.hom).1 h, fun y ↦ ⟨y ≫ eH.inv, by simp⟩⟩


end CategoryTheory.Endofunctor.IsoAlgebra
