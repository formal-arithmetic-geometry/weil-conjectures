/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Balanced derived coefficient associators commute with shifts

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-associator-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}

variable {p : Scalars.{c, v, r} J}
  (n : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) p)




private theorem kanPostShift
    {D D' L : Type*} [Category D] [HasShift D ℤ]
    [Category D'] [HasShift D' ℤ] [Category L] [HasShift L ℤ]
    (F : D ⥤ D') (Q : D ⥤ L)
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) :
    (LF ⋙ shiftFunctor D' n).IsRightKanExtension
      ((associator Q LF (shiftFunctor D' n)).inv ≫
        whiskerRight α (shiftFunctor D' n)) := by
  let P := Functor.RightExtension.postcompose₂ Q F (shiftFunctor D' n)
  let : IsIso (𝟙 (F ⋙ shiftFunctor D' n)) := by infer_instance
  let : P.IsEquivalence := by
    dsimp [P, Functor.RightExtension.postcompose₂]
    let t : ((whiskeringRight L D' D').obj (shiftFunctor D' n)) ⋙
        (whiskeringLeft D L D').obj Q ⟶
        (whiskeringLeft D L D').obj Q ⋙
          ((whiskeringRight D D' D').obj (shiftFunctor D' n)) :=
      { app G := (associator Q G (shiftFunctor D' n)).inv }
    let : IsIso t := by apply NatIso.isIso_of_isIso_app
    exact CostructuredArrow.isEquivalenceMap₂ t (𝟙 _)
  constructor
  refine ⟨Limits.IsTerminal.ofIso
    (Limits.IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact Functor.RightExtension.postcompose₂ObjMkIso (shiftFunctor D' n) α

private theorem kanMap_commShift
    {D D' L : Type*} [Category D] [HasShift D ℤ]
    [Category D'] [HasShift D' ℤ] [Category L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ] (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') [LF.CommShift ℤ] (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] [NatTrans.CommShift α ℤ]
    (G : L ⥤ D') [G.CommShift ℤ] (β : Q ⋙ G ⟶ F) [NatTrans.CommShift β ℤ]
    (τ : G ⟶ LF) (hτ : whiskerLeft Q τ ≫ α = β) :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  let γ := (associator Q LF (shiftFunctor D' n)).inv ≫
    whiskerRight α (shiftFunctor D' n)
  let : (LF ⋙ shiftFunctor D' n).IsRightKanExtension γ := kanPostShift F Q LF α n
  apply (LF ⋙ shiftFunctor D' n).hom_ext_of_isRightKanExtension γ
  ext X
  simp only [γ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, Category.id_comp, Category.assoc]
  apply (cancel_epi (G.map ((Q.commShiftIso n).hom.app X))).mp
  have fac (X : D) : τ.app (Q.obj X) ≫ α.app X = β.app X :=
    NatTrans.congr_app hτ X
  rw [← (shiftFunctor D' n).map_comp, fac]
  have hβ := NatTrans.shift_app_comm β n X
  have hα := NatTrans.shift_app_comm α n X
  simp only [commShiftIso_comp_hom_app, Category.assoc] at hβ hα
  rw [hβ]
  have hn := τ.naturality ((Q.commShiftIso n).hom.app X)
  dsimp at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [hα, ← Category.assoc, fac]


private theorem homotopyComp_commShift
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom ℤ := by
  have hc : NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom ℤ := by
    constructor
    intro n
    ext K i
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.commShiftIso_comp_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    rfl
  have hf (K : CochainComplex A ℤ) :
      (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hg (K : CochainComplex B ℤ) :
      (G.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hh (K : CochainComplex A ℤ) :
      (H.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  have he : whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom =
      (Functor.associator _ _ _).inv ≫
        whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft (F.mapHomologicalComplex (.up ℤ))
          (G.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom _ ≫
        (H.mapHomotopyCategoryFactors (.up ℤ)).inv := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp]
    rw [hf, hg, hh]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.comp_id]
    erw [Category.id_comp, Category.id_comp]
    rfl
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient A (.up ℤ))
    (fun K ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective K).choose_spec ▸
      inferInstance⟩)

variable [scalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (p a).derived.CommShift ℤ]
  (canonical : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    NatTrans.CommShift (p a).counit ℤ)

include canonical

private def compositeCounit {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) :
    DerivedCategory.Qh ⋙ ((p a).derived ⋙ (p b).derived) ⟶
      (p (a ≫ b)).ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight (p a).counit (p b).derived ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft ((p a).ordinary.mapHomotopyCategory (.up ℤ)) (p b).counit ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (Functor.mapHomotopyCategoryCompIso (n.ordinary a b) (.up ℤ)).hom _

private theorem compositeCounit_commShift {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) : NatTrans.CommShift (compositeCounit n a b) ℤ := by
  have := canonical a
  have := canonical b
  have := homotopyComp_commShift (n.ordinary a b)
  dsimp only [compositeCounit]
  infer_instance

/-- Balanced scalar associators commute with the counit-normalized shifts.
Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 07A6
(blueprint: lem-pur-coefficient-associator-shifts).

Proof: the ordinary comparison mapped termwise commutes with shifts degreewise.
Its composite with the two universal counits therefore commutes with shifts.
Take its universal lift to the derived functor for the composite coefficient map.
Kan uniqueness gives shift compatibility of this lift. On a flat-term K-flat
representative the normalization equation and invertibility of its counit identify
this lift with the given balanced associator. Resolve arbitrary complexes by such
representatives and use naturality to obtain equality on every derived object. -/
theorem coefficientAssociatorShifts
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    NatTrans.CommShift (n.derived a b).hom ℤ := by
  let L := (p (a ≫ b)).derived
  let α := (p (a ≫ b)).counit
  let G := (p a).derived ⋙ (p b).derived
  let β := compositeCounit n a b
  let := (p (a ≫ b)).universal
  let : L.IsRightKanExtension α :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso _ (.up ℤ))
  let t : G ⟶ L := L.liftOfIsRightKanExtension α G β
  have ht : whiskerLeft DerivedCategory.Qh t ≫ α = β :=
    L.liftOfIsRightKanExtension_fac α G β
  have hflat (P : CochainComplex (Mod J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
      t.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) =
        (n.derived a b).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) := by
    let := n.computed (a ≫ b) P hP hf
    apply (cancel_mono (α.app ((HomotopyCategory.quotient _ _).obj P))).1
    have h := NatTrans.congr_app ht ((HomotopyCategory.quotient _ _).obj P)
    change t.app _ ≫ α.app _ = β.app _ at h
    rw [h]
    simpa only [β, α, compositeCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp] using (n.representative a b P hP hf).symm
  have hall (H : HomotopyCategory (Mod J R) (.up ℤ)) :
      t.app (DerivedCategory.Qh.obj H) = (n.derived a b).hom.app
        (DerivedCategory.Qh.obj H) := by
    obtain ⟨P₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
    obtain ⟨P, f, hP, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
    have hf' (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) :=
      ObjectProperty.prop_of_iso (exactFunctor _ _)
        (siteSheafTensorRightIso R _).symm (hf i)
    let q := (HomotopyCategory.quotient (Mod J R) (.up ℤ)).map f
    have hq' : HomotopyCategory.quasiIso _ _ q :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
    let : IsIso (DerivedCategory.Qh.map q) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) q hq'
    have hEq := congrArg (fun h ↦ h ≫ L.map (DerivedCategory.Qh.map q))
      (hflat P hP hf')
    rw [← t.naturality, ← (n.derived a b).hom.naturality] at hEq
    exact (cancel_epi (G.mapIso (asIso (DerivedCategory.Qh.map q))).hom).1 hEq
  have heq : t = (n.derived a b).hom := by
    ext M
    let e := DerivedCategory.Qh.objObjPreimageIso M
    apply (cancel_epi (G.mapIso e).hom).1
    change G.map e.hom ≫ t.app M = G.map e.hom ≫ (n.derived a b).hom.app M
    rw [t.naturality, (n.derived a b).hom.naturality, hall]
  have := canonical (a ≫ b)
  have := compositeCounit_commShift n canonical a b
  have h : NatTrans.CommShift t ℤ :=
    kanMap_commShift _ DerivedCategory.Qh L α G β t ht
  rw [heq] at h
  exact h

end SheafOfModules.RingedCoefficientProjection
