/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteReductionSystem
import Sheaf.Paper.FiniteReductionSystemCoherence
import Sheaf.Paper.FiniteReductionDerivedExtension
import Sheaf.Paper.FiniteReductionFlatExtension
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! Construction of normalized coherent finite reduction systems. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u vC vD vH vK wC wD wH wK uC uD uH uK
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.FiniteReduction

attribute [local irreducible] extend ordinaryComparison ordinaryAssociator

private theorem derived_of_resolution_computations
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasDerivedCategory C]
    (F : CochainComplex C ℤ ⥤ D) (L G : DerivedCategory C ⥤ D)
    (ε : DerivedCategory.Q ⋙ L ⟶ F) (β : DerivedCategory.Q ⋙ G ⟶ F)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso C (.up ℤ))]
    (hres : ∀ P : CochainComplex C ℤ,
      ∃ (R : CochainComplex C ℤ) (f : R ⟶ P),
        QuasiIso f ∧ IsIso (ε.app R) ∧ IsIso (β.app R)) :
    G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso C (.up ℤ)) := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let τ := L.leftDerivedLift ε W G β
  have hτ : ∀ K, IsIso (τ.app K) := by
    intro K
    let P := DerivedCategory.Q.objPreimage K
    let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨R, f, hf, hε, hβ⟩ := hres P
    let := hf
    let := hε
    let := hβ
    have hfac : τ.app (DerivedCategory.Q.obj R) ≫ ε.app R = β.app R :=
      L.leftDerived_fac_app ε W G β R
    have : IsIso (τ.app (DerivedCategory.Q.obj R)) := by
      rw [← isIso_comp_right_iff _ (ε.app R), hfac]
      infer_instance
    let j : DerivedCategory.Q.obj R ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ e
    have hnat := τ.naturality j.hom
    have : IsIso (G.map j.hom ≫ τ.app K) := by
      rw [hnat]
      infer_instance
    exact (isIso_comp_left_iff (G.map j.hom) _).mp this
  let : IsIso τ := (NatTrans.isIso_iff_isIso_app τ).mpr hτ
  exact (L.isLeftDerivedFunctor_iff_isIso_leftDerivedLift ε W G β).mpr inferInstance

private theorem exists_normalized_derived_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasDerivedCategory C]
    (F : CochainComplex C ℤ ⥤ D) (L G : DerivedCategory C ⥤ D)
    (ε : DerivedCategory.Q ⋙ L ⟶ F) (β : DerivedCategory.Q ⋙ G ⟶ F)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso C (.up ℤ))]
    (hres : ∀ P : CochainComplex C ℤ,
      ∃ (R : CochainComplex C ℤ) (f : R ⟶ P),
        QuasiIso f ∧ IsIso (ε.app R) ∧ IsIso (β.app R)) :
    ∃ i : G ≅ L, ∀ P : CochainComplex C ℤ,
      i.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = β.app P := by
  let : G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso C (.up ℤ)) :=
    derived_of_resolution_computations F L G ε β hres
  let i := Functor.leftDerivedUnique L G β ε (HomologicalComplex.quasiIso C (.up ℤ))
  refine ⟨i, fun P ↦ ?_⟩
  simpa only [i, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
    Functor.leftDerivedNatTrans_app G L β ε (HomologicalComplex.quasiIso C (.up ℤ))
      (𝟙 F) P

private def compositeCounit
    {C D H : Type*} [Category C] [Category D] [Category H]
    [Abelian C] [Abelian D] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    (F : C ⥤ D) (G : D ⥤ H) (FG : C ⥤ H)
    [F.Additive] [G.Additive] [FG.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory H)
    (εF : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (i : F ⋙ G ≅ FG) : DerivedCategory.Q ⋙ (LF ⋙ LG) ⟶
      FG.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight εF LG ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) εG ≫
    Functor.whiskerRight (Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom
      DerivedCategory.Q

private theorem compositeCounit_app
    {C D H : Type*} [Category C] [Category D] [Category H]
    [Abelian C] [Abelian D] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    (F : C ⥤ D) (G : D ⥤ H) (FG : C ⥤ H)
    [F.Additive] [G.Additive] [FG.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory H)
    (εF : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (i : F ⋙ G ≅ FG) (P : CochainComplex C ℤ) :
    (compositeCounit F G FG LF LG εF εG i).app P =
      LG.map (εF.app P) ≫ εG.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso i (.up ℤ)).hom.app P) := rfl

private theorem reverse_normalization
    {C : Type*} [Category C] {X Y Z W : C}
    (i : X ≅ Y) (α : Y ⟶ Z) (β : X ⟶ W) (e : Z ≅ W)
    (h : i.hom ≫ α = β ≫ e.inv) : i.inv ≫ β = α ≫ e.hom := by
  apply (cancel_epi i.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp

private theorem compositeCounit_isIso
    {C D H : Type*} [Category C] [Category D] [Category H]
    [Abelian C] [Abelian D] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    (F : C ⥤ D) (G : D ⥤ H) (FG : C ⥤ H)
    [F.Additive] [G.Additive] [FG.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory H)
    (εF : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (i : F ⋙ G ≅ FG) (P : CochainComplex C ℤ)
    [IsIso (εF.app P)]
    [IsIso (εG.app ((F.mapHomologicalComplex (.up ℤ)).obj P))] :
    IsIso ((compositeCounit F G FG LF LG εF εG i).app P) := by
  dsimp only [compositeCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

private theorem exists_composite_iso_of_flat
    {C : Type uC} {D : Type uD} {H : Type uH}
    [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
    [Abelian C] [Abelian D] [Abelian H]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wH} H]
    (F : C ⥤ D) (G : D ⥤ H) (FG : C ⥤ H)
    [F.Additive] [G.Additive] [FG.Additive] [F.PreservesFlat] [F.IsLeftAdjoint]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory H)
    (LFG : DerivedCategory C ⥤ DerivedCategory H)
    (εF : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εFG : DerivedCategory.Q ⋙ LFG ⟶ FG.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [LFG.IsLeftDerivedFunctor εFG (HomologicalComplex.quasiIso C (.up ℤ))]
    (hF : ∀ P, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P → IsIso (εF.app P))
    (hG : ∀ P, (HomologicalComplex.quasiIso D (.up ℤ)).kFlat P → IsIso (εG.app P))
    (hFG : ∀ P, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P → IsIso (εFG.app P))
    (i : F ⋙ G ≅ FG) :
    ∃ j : LF ⋙ LG ≅ LFG, ∀ P : CochainComplex C ℤ,
      j.hom.app (DerivedCategory.Q.obj P) ≫ εFG.app P =
        (compositeCounit F G FG LF LG εF εG i).app P := by
  let Λ₀ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  let Λ := Λ₀.reduced
  apply exists_normalized_derived_iso
  intro P
  let R := Λ.resolutionFunctor.obj P
  have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P
  have hkF := F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
    ObjectProperty.flat.essImage_ι_le P
  have := hF R hk
  have := hG ((F.mapHomologicalComplex (.up ℤ)).obj R) hkF
  exact ⟨R, Λ.resolutionNatTrans.app P, inferInstance, hFG R hk,
    compositeCounit_isIso _ _ _ _ _ _ _ _ R⟩

private theorem quotient_surjective (l : ℕ) {r m : ℕ} (h : m ≤ r) :
    Function.Surjective (quotient.{u} l h) := by
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow l h) y.down.down
  exact ⟨⟨⟨x⟩⟩, congrArg (fun z ↦ (⟨⟨z⟩⟩ : Coeff.{u} l m)) hx⟩

private theorem exists_site_associator
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime]
    (D : ∀ (r m : ℕ) (h : m ≤ r), DerivedExtension J (quotient.{u} l h))
    (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m) :
    ∃ i : (D r m hmr).functor ⋙ (D m n hnm).functor ≅
        (D r n (hnm.trans hmr)).functor,
      ∀ P : CochainComplex (Sheaf J (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ,
      i.hom.app (DerivedCategory.Q.obj P) ≫ (D r n (hnm.trans hmr)).counit.app P =
      (compositeCounit (extend J (quotient l hmr)) (extend J (quotient l hnm))
        (extend J (quotient l (hnm.trans hmr))) (D r m hmr).functor
        (D m n hnm).functor (D r m hmr).counit (D m n hnm).counit
        (ordinaryAssociator J l hmr hnm)).app P := by
  let F := extend J (quotient.{u} l hmr)
  let : F.PreservesFlat := ⟨fun hX ↦
    flat_extend_of_surjective J (quotient l hmr) (quotient_surjective l hmr) hX⟩
  let : F.IsLeftAdjoint := (extendAdjunction J (quotient l hmr)).isLeftAdjoint
  let : (D r n (hnm.trans hmr)).functor.IsLeftDerivedFunctor
      (D r n (hnm.trans hmr)).counit (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    (D r n (hnm.trans hmr)).universal
  exact exists_composite_iso_of_flat F (extend J (quotient l hnm))
    (extend J (quotient l (hnm.trans hmr))) (D r m hmr).functor (D m n hnm).functor
    (D r n (hnm.trans hmr)).functor (D r m hmr).counit (D m n hnm).counit
    (D r n (hnm.trans hmr)).counit (D r m hmr).computation (D m n hnm).computation
    (D r n (hnm.trans hmr)).computation (ordinaryAssociator J l hmr hnm)

private theorem universal_of_kFlat_computation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [HasDerivedCategory.{wC} C]
    [MonoidalCategory (CochainComplex C ℤ)]
    [(HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]
    (F : CochainComplex C ℤ ⥤ D) (L : DerivedCategory C ⥤ D)
    (ε : DerivedCategory.Q ⋙ L ⟶ F)
    (hε : ∀ P, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P → IsIso (ε.app P)) :
    L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso C (.up ℤ)) := by
  exact (HomologicalComplex.quasiIso C (.up ℤ)).localizerMorphismKFlat
    |>.isLeftDerivedFunctor_of_isLeftDerivabilityStructure ε (fun P ↦ hε P.obj P.property)

private theorem exists_normalized_comparison
    {C : Type uC} {D : Type uD} {H : Type uH} {K : Type uK}
    [Category.{vC} C] [Category.{vD} D] [Category.{vH} H] [Category.{vK} K]
    [Abelian C] [Abelian D] [Abelian H] [Abelian K]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasDerivedCategory.{wH} H] [HasDerivedCategory.{wK} K]
    (F : C ⥤ H) (G : D ⥤ K) (Cr : C ⥤ D) (Cm : H ⥤ K)
    [F.Additive] [G.Additive] [Cr.Additive] [Cm.Additive]
    [Cr.PreservesFlat] [Cr.IsLeftAdjoint]
    (LF : DerivedCategory C ⥤ DerivedCategory H)
    (LG : DerivedCategory D ⥤ DerivedCategory K)
    (CrD : DerivedCategory C ⥤ DerivedCategory D)
    (CmD : DerivedCategory H ⥤ DerivedCategory K)
    (εF : DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εG : DerivedCategory.Q ⋙ LG ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δr : DerivedCategory.Q ⋙ CrD ≅ Cr.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δm : DerivedCategory.Q ⋙ CmD ≅ Cm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hF : ∀ Q, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q → IsIso (εF.app Q))
    (hG : ∀ Q, (HomologicalComplex.quasiIso D (.up ℤ)).kFlat Q → IsIso (εG.app Q))
    (χ : F ⋙ Cm ≅ Cr ⋙ G) :
    ∃ i : LF ⋙ CmD ≅ CrD ⋙ LG, ∀ Q : CochainComplex C ℤ,
      i.hom.app (DerivedCategory.Q.obj Q) ≫ LG.map (δr.hom.app Q) ≫
          εG.app ((Cr.mapHomologicalComplex (.up ℤ)).obj Q) =
        CmD.map (εF.app Q) ≫ δm.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).hom.app Q) := by
  let H := (F ⋙ Cm).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let L := LF ⋙ CmD
  let R := CrD ⋙ LG
  let α : DerivedCategory.Q ⋙ L ⟶ H :=
    Functor.whiskerRight εF CmD ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) δm.hom
  let β := compositeCounit Cr G (F ⋙ Cm) CrD LG
    δr.hom εG χ.symm
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  have hcomp : ∀ Q, W.kFlat Q → IsIso (α.app Q) := by
    intro Q hQ
    have := hF Q hQ
    dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let : L.IsLeftDerivedFunctor α W := universal_of_kFlat_computation H L α hcomp
  obtain ⟨i, hi⟩ := exists_composite_iso_of_flat Cr G (F ⋙ Cm)
    CrD LG L δr.hom εG α
    (fun Q _ ↦ inferInstance) hG hcomp χ.symm
  refine ⟨i.symm, fun Q ↦ ?_⟩
  have hQ := hi Q
  rw [compositeCounit_app] at hQ
  dsimp only [α, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hQ
  simpa only [Category.assoc, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Iso.app_hom] using
    reverse_normalization (i.app (DerivedCategory.Q.obj Q))
      (CmD.map (εF.app Q) ≫
        δm.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Q))
      (LG.map (δr.hom.app Q) ≫
        εG.app ((Cr.mapHomologicalComplex (.up ℤ)).obj Q))
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex χ (.up ℤ)).app Q))
      (by
        simpa only [Category.assoc, Functor.mapHomologicalComplexCompIso,
        NatIso.mapHomologicalComplex, Iso.symm_hom,
        Functor.mapIso_inv, Iso.app_inv, Iso.app_hom] using hQ)

private theorem exists_comparison
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r m : ℕ) (hmr : m ≤ r)
    (E : DerivedExtension T.smallEtaleTopology (quotient.{u} l hmr))
    (P : DerivedExtension (Scheme.ProEt.topology T) (quotient.{u} l hmr)) :
    let Cr := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T
    let Cm := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l m)) T
    let F := extend T.smallEtaleTopology (quotient.{u} l hmr)
    ∃ i : E.functor ⋙ Cm.mapDerivedCategory ≅ Cr.mapDerivedCategory ⋙ P.functor,
    ∀ Q : CochainComplex
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r))) ℤ,
      i.hom.app (DerivedCategory.Q.obj Q) ≫
        P.functor.map (Cr.mapDerivedCategoryFactors.hom.app Q) ≫
        P.counit.app ((Cr.mapHomologicalComplex (.up ℤ)).obj Q) =
      Cm.mapDerivedCategory.map (E.counit.app Q) ≫
        Cm.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((ordinaryComparisonComplex T (quotient l hmr)).hom.app Q) := by
  exact exists_normalized_comparison
    (extend T.smallEtaleTopology (quotient l hmr))
    (extend (Scheme.ProEt.topology T) (quotient l hmr))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l r)) T)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (Coeff.{u} l m)) T)
    E.functor P.functor _ _ E.counit P.counit
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategoryFactors
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategoryFactors
    E.computation P.computation (ordinaryComparison T (quotient l hmr))

/-- The ordinary scalar-extension adjunctions admit a coherent universal derived system.
Source: Stacks Tags 06XN, 06YT, 06YY and 03EL; blueprint sk-lem-sp-reduction,
first paragraph (blueprint: lem-pur-finite-reduction-system-existence).

Proof: derive each sheafified tensor functor using K-flat resolutions. Restriction of
scalars is exact and conservative, and identifies extension with tensoring by the
constant target ring; hence extension preserves quasi-isomorphisms between K-flat
complexes. A bounded-above flat resolution is taken to a bounded-above flat complex,
and filtered colimits of these resolutions remain K-flat. This gives the universal
counit and its invertibility on K-flat complexes. Exact site comparison preserves flat
complexes and their K-flat resolutions. Derive ordinaryComparison and ordinaryAssociator
by their universal properties. Their components on flat K-flat representatives satisfy
the three normalization equations in System. The two ordinary comparison-associator
routes are mates of the identity on the same composite scalar restriction functor;
uniqueness of adjoints makes them equal. Compute on K-flat resolutions and cancel the
invertible counits to obtain CoherentAt for every object, independently of its resolution.
This construction works also for exponent zero (the zero coefficient ring). -/
theorem exists_coherent_system (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    ∃ S : System T l, ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
      (K : DerivedCategory
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))),
      S.CoherentAt r m n hmr hnm K := by
  classical
  let E (r m : ℕ) (h : m ≤ r) :=
    Classical.choice (nonempty_derivedExtension T.smallEtaleTopology (quotient.{u} l h))
  let P (r m : ℕ) (h : m ≤ r) :=
    Classical.choice (nonempty_derivedExtension (Scheme.ProEt.topology T) (quotient.{u} l h))
  choose c hc using fun (r m : ℕ) (h : m ≤ r) ↦
    exists_comparison T l r m h (E r m h) (P r m h)
  choose ae hae using fun (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m) ↦
    exists_site_associator T.smallEtaleTopology l E r m n hmr hnm
  choose ap hap using fun (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m) ↦
    exists_site_associator (Scheme.ProEt.topology T) l P r m n hmr hnm
  let S : System T l :=
    { etale := E
      proetale := P
      comparison := c
      comparison_model := fun r m h Q _ _ ↦ hc r m h Q
      etaleAssociator := ae
      proetaleAssociator := ap
      etaleAssociator_model := by
        intro r m n hmr hnm Q _ _
        exact hae r m n hmr hnm Q
      proetaleAssociator_model := by
        intro r m n hmr hnm Q _ _
        exact hap r m n hmr hnm Q }
  exact ⟨S, fun r m n hmr hnm K ↦ System.coherentAt T l S r m n hmr hnm K⟩

end AlgebraicGeometry.FiniteReduction
