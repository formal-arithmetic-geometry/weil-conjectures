/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ExceptionalForgetCounit

/-! # Invertibility of the canonical exceptional forget mate -/

@[expose] public noncomputable section

universe v v'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category.{v} C] [Abelian C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

/-- The canonical forget comparison for the derived lift on full subcategories has an
invertible mate under the exceptional adjunctions. -/
theorem isIso_mateEquiv_restrictedDerivedForget_app
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
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
    let U := PCW.liftFullSubcategory PC (forget F).mapDerivedCategory
      (fun M hM ↦ (hPCW M).1 hM)
    let V := PDW.liftFullSubcategory PD (forget G).mapDerivedCategory
      (fun M hM ↦ (hPDW M).1 hM)
    let β : PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW ⋙ V ≅
        U ⋙ PC.liftFullSubcategory PD L.rightDerivedFunctor hR :=
      NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ((derivedForgetCommIso e).app M.obj))
        (fun g ↦ ObjectProperty.hom_ext _ ((derivedForgetCommIso e).hom.naturality g.hom))
    IsIso ((mateEquiv adjW adj (TwoSquare.mk _ _ _ _ β.inv)).app L') := by
  dsimp only
  obtain ⟨H, hH, eH, d, hd, hfree⟩ :=
    exists_bijective_rightDerivedFunctor_map_comp_free_with_forget e PC PD hPC
      hR adj hPC_F hPD_G hcoprod L'.obj ((hPDW _).1 L'.property)
  let T := PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW
  have hb (M : PCW.FullSubcategory) : Function.Bijective
      (fun u : M ⟶ ⟨H, (hPCW H).2 hH⟩ ↦ T.map u ≫ ObjectProperty.homMk d) := by
    have h := bijective_rightDerivedFunctor_map_comp e PC hPC_shift d hfree M.obj
      ((hPCW _).1 M.property)
    refine ⟨fun u u' huu ↦ ObjectProperty.hom_ext _ (h.1 (congrArg InducedCategory.Hom.hom huu)),
      fun y ↦ ?_⟩
    obtain ⟨u, hu⟩ := h.2 y.hom
    exact ⟨ObjectProperty.homMk u, ObjectProperty.hom_ext _ hu⟩
  apply Adjunction.isIso_mateEquiv_app_of_universalArrow adjW adj _
    (A := ⟨H, (hPCW H).2 hH⟩) (ObjectProperty.homMk d) hb (ObjectProperty.isoMk _ eH)
  apply ObjectProperty.hom_ext
  change (derivedForgetCommIso e).inv.app H ≫ (forget G).mapDerivedCategory.map d = _
  rw [hd, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Endofunctor.IsoAlgebra
