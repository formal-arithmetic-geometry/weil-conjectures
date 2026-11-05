/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointForget

/-!
# The counit of the lifted right adjoint lies over the geometric counit

In the setting of `CategoryTheory.Endofunctor.IsoAlgebra.nonempty_forget_obj_iso_of_adjunction`,
let `R'` be a right adjoint of the restriction `RL : P_C ⥤ P_D` of the right derived functor of
`L`, and `RW` any right adjoint of the restriction of the right derived functor of the lift
`mapOfNatIso e`. Then there is an isomorphism `eH : U (RW L') ≅ R' (U L')` of underlying objects
under which the image of the counit `RW_der (RW L') ⟶ L'` under the forgetful functor `U` is the
counit of `R'`, up to the comparison `RW_der ⋙ U ≅ U ⋙ RL`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_map_counit_eq`).

This upgrades `CategoryTheory.Endofunctor.IsoAlgebra.nonempty_forget_obj_iso_of_adjunction` (which
only gives an abstract isomorphism) to a statement about the counits, which is what is needed to
show that base change maps of the forgetful functor along `RW` and `R'` are invertible.
-/

@[expose] public noncomputable section

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

/-- **The lifted counit on free algebras, with its underlying morphism.** The statement of
`CategoryTheory.Endofunctor.IsoAlgebra.exists_bijective_rightDerivedFunctor_map_comp_free`, also
recording that the underlying morphism of `d : RW H ⟶ L'` is the counit `RL (R' Y) ⟶ Y` of `R'`,
up to `eH` and the comparison `RW ⋙ U ≅ U ⋙ RL`. -/
theorem exists_bijective_rightDerivedFunctor_map_comp_free_of_forget_map_eq
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
    ∃ (H : DerivedCategory (IsoAlgebra F))
      (eH : (forget F).mapDerivedCategory.obj H ≅ (R'.obj ⟨_, hL'⟩).obj)
      (d : (mapOfNatIso e).rightDerivedFunctor.obj H ⟶ L'),
      (forget G).mapDerivedCategory.map d = (derivedForgetCommIso e).hom.app H ≫
        L.rightDerivedFunctor.map eH.hom ≫ (adj.counit.app ⟨_, hL'⟩).hom ∧
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
  refine ⟨H, eH, d, hd, fun X hX ↦ ?_⟩
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

omit [Abelian C] [IsGrothendieckAbelian.{v} C] [F.Additive] [F.IsEquivalence] [Abelian D]
  [IsGrothendieckAbelian.{v'} D] [G.Additive] [G.IsEquivalence] [L.Additive]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C] in
/-- A morphism `d : T H ⟶ Y` such that `u ↦ T u ≫ d` is bijective on morphisms out of every
object is a universal arrow: its adjoint `H ⟶ R Y` is an isomorphism, for any right adjoint `R`
of `T`. -/
lemma isIso_homEquiv_of_bijective {A B : Type*} [Category* A] [Category* B] {T : A ⥤ B}
    {R : B ⥤ A} (adj : T ⊣ R) {H : A} {Y : B} (d : T.obj H ⟶ Y)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ H ↦ T.map u ≫ d)) :
    IsIso (adj.homEquiv _ _ d) := by
  have hφ (M : A) : Function.Bijective (fun u : M ⟶ H ↦ u ≫ adj.homEquiv _ _ d) := by
    have h : (fun u : M ⟶ H ↦ u ≫ adj.homEquiv _ _ d) =
        adj.homEquiv M Y ∘ (fun u : M ⟶ H ↦ T.map u ≫ d) := by
      funext u
      exact (adj.homEquiv_naturality_left u d).symm
    rw [h]
    exact (Equiv.bijective _).comp (hd M)
  obtain ⟨s, hs⟩ := (hφ (R.obj Y)).2 (𝟙 _)
  refine ⟨s, (hφ H).1 ?_, hs⟩
  dsimp only at hs ⊢
  rw [Category.assoc, hs, Category.comp_id, Category.id_comp]

/-- **The counit of the lifted right adjoint lies over the geometric counit.** In the setting of
`CategoryTheory.Endofunctor.IsoAlgebra.nonempty_forget_obj_iso_of_adjunction`, for every `L'` in
`P_D^W` there is an isomorphism `eH : U (RW L') ≅ R' (U L')` of underlying objects such that the
underlying morphism of the counit `RW_der (RW L') ⟶ L'` is
`U (RW_der (RW L')) ≅ RL (U (RW L')) --RL eH--> RL (R' (U L')) --ε--> U L'`, `ε` being the counit
of `R'`. -/
theorem exists_forget_map_counit_eq
    (PC : ObjectProperty (DerivedCategory C)) (PD : ObjectProperty (DerivedCategory D))
    [PC.IsClosedUnderIsomorphisms] [PD.IsClosedUnderIsomorphisms]
    (hPC : ∀ K, PC K → DerivedCategory.TStructure.t.bounded K)
    (hPC_shift : ∀ (K : DerivedCategory C) (n : ℤ), PC K → PC (K⟦n⟧))
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    {R' : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L.rightDerivedFunctor hR ⊣ R')
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    (PCW : ObjectProperty (DerivedCategory (IsoAlgebra F)))
    (PDW : ObjectProperty (DerivedCategory (IsoAlgebra G)))
    (hPCW : ∀ M, PCW M ↔ PC ((forget F).mapDerivedCategory.obj M))
    (hPDW : ∀ M, PDW M ↔ PD ((forget G).mapDerivedCategory.obj M))
    (hRW : ∀ M, PCW M → PDW ((mapOfNatIso e).rightDerivedFunctor.obj M))
    {RW : PDW.FullSubcategory ⥤ PCW.FullSubcategory}
    (adjW : PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW ⊣ RW)
    (L' : PDW.FullSubcategory) :
    ∃ eH : (forget F).mapDerivedCategory.obj (RW.obj L').obj ≅
        (R'.obj ⟨(forget G).mapDerivedCategory.obj L'.obj, (hPDW _).1 L'.property⟩).obj,
      (forget G).mapDerivedCategory.map (adjW.counit.app L').hom =
        (derivedForgetCommIso e).hom.app (RW.obj L').obj ≫ L.rightDerivedFunctor.map eH.hom ≫
          (adj.counit.app ⟨_, (hPDW _).1 L'.property⟩).hom := by
  obtain ⟨H, eH, d, hdc, hd⟩ :=
    exists_bijective_rightDerivedFunctor_map_comp_free_of_forget_map_eq e PC PD hPC hR adj
      hPC_F hPD_G hcoprod L'.obj ((hPDW _).1 L'.property)
  have hH : PCW H := (hPCW H).2 (PC.prop_of_iso eH.symm (R'.obj _).property)
  let T := PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW
  have hb (M : PCW.FullSubcategory) : Function.Bijective
      (fun u : M ⟶ ⟨H, hH⟩ ↦ T.map u ≫ ObjectProperty.homMk d) := by
    have h := bijective_rightDerivedFunctor_map_comp e PC hPC_shift d hd M.obj
      ((hPCW _).1 M.property)
    refine ⟨fun u u' huu ↦ ObjectProperty.hom_ext _ (h.1 (congrArg InducedCategory.Hom.hom huu)),
      fun y ↦ ?_⟩
    obtain ⟨u, hu⟩ := h.2 y.hom
    exact ⟨ObjectProperty.homMk u, ObjectProperty.hom_ext _ hu⟩
  let d' : T.obj ⟨H, hH⟩ ⟶ L' := ObjectProperty.homMk d
  let i := adjW.homEquiv _ _ d'
  have : IsIso i := isIso_homEquiv_of_bijective adjW _ hb
  have hi : T.map i ≫ adjW.counit.app L' = d' :=
    (adjW.homEquiv_counit (g := i)).symm.trans ((adjW.homEquiv _ _).symm_apply_apply d')
  have hi' : (T.map i).hom ≫ (adjW.counit.app L').hom = d := congrArg InducedCategory.Hom.hom hi
  have hT : (mapOfNatIso e).rightDerivedFunctor.map (inv i).hom ≫ (T.map i).hom = 𝟙 _ := by
    have h := congrArg InducedCategory.Hom.hom (T.congr_map (IsIso.inv_hom_id i))
    rw [T.map_comp, T.map_id] at h
    exact h
  refine ⟨(forget F).mapDerivedCategory.mapIso (PCW.ι.mapIso (asIso i)).symm ≪≫ eH, ?_⟩
  have hn := (derivedForgetCommIso e).hom.naturality (inv i).hom
  dsimp at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv,
    ObjectProperty.ι_map, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← hdc, ← Functor.map_comp, ← hi', ← Category.assoc, hT, Category.id_comp]

end CategoryTheory.Endofunctor.IsoAlgebra
