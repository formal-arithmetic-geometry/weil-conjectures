/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

/-! # Descent of a termwise coefficient map
Source: Stacks Project, Tags 06XN, 05SU and 06YY.
(blueprint: lem-sbc-derived-coefficient-map-descent)
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

private theorem kanPostShift
    {D D' L : Type*} [Category D] [HasShift D ℤ]
    [Category D'] [HasShift D' ℤ] [Category L] [HasShift L ℤ]
    (F : D ⥤ D') (Q : D ⥤ L)
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) :
    (LF ⋙ shiftFunctor D' n).IsRightKanExtension
      ((associator Q LF (shiftFunctor D' n)).inv ≫
        whiskerRight α (shiftFunctor D' n)) := by
  let P := RightExtension.postcompose₂ Q F (shiftFunctor D' n)
  let : IsIso (𝟙 (F ⋙ shiftFunctor D' n)) := by infer_instance
  let : P.IsEquivalence := by
    dsimp [P, RightExtension.postcompose₂]
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
  exact RightExtension.postcompose₂ObjMkIso (shiftFunctor D' n) α

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


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem pro_preserves_at
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T) (X : C)
    (hc : ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) Y) :
    Q.HasPointwiseRightKanExtensionAt F (Q.obj X) ∧
      PreservesLimit (StructuredArrow.proj (Q.obj X) Q ⋙ F) H := by
  classical
  obtain ⟨Y, hY⟩ := hc
  obtain ⟨u, j₀, r, hr, hfactor⟩ := hY.2
  obtain ⟨hlim, π, ⟨hπ⟩, hden, _⟩ :=
    leftDerived_defined_pointwiseKan_bridge W Q F X Y hY u ⟨j₀, r, hr, hfactor⟩
  let u' : (Functor.const (W.Over ⊤ X)).obj (H.obj Y) ⟶
      MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ (F ⋙ H) :=
    { app := fun j ↦ H.map (u.app j)
      naturality := by
        intro i j f
        change 𝟙 _ ≫ H.map (u.app j) = H.map (u.app i) ≫ H.map (F.map f.left)
        rw [Category.id_comp, ← H.map_comp]
        exact H.congr_map (by simpa using u.naturality f) }
  have hr' : u'.app j₀ ≫ H.map r = 𝟙 (H.obj Y) := by
    change H.map (u.app j₀) ≫ H.map r = _
    rw [← H.map_comp, hr]
    exact H.map_id Y
  have hfactor' : ∀ j : W.Over ⊤ X, ∃ (k : W.Over ⊤ X) (a : k ⟶ j₀) (b : k ⟶ j),
      (F ⋙ H).map b.left = (F ⋙ H).map a.left ≫ H.map r ≫ u'.app j := by
    intro j
    obtain ⟨k, a, b, hab⟩ := hfactor j
    refine ⟨k, a, b, ?_⟩
    change H.map (F.map b.left) = _
    change F.map b.left = F.map a.left ≫ r ≫ u.app j at hab
    simp only [hab, H.map_comp]
    rfl
  have hY' : IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ (F ⋙ H)) (H.obj Y) :=
    ⟨hY.1, u', j₀, H.map r, hr', hfactor'⟩
  obtain ⟨_, π', ⟨hπ'⟩, hden', _⟩ :=
    leftDerived_defined_pointwiseKan_bridge W Q (F ⋙ H) X (H.obj Y) hY' u'
      ⟨j₀, H.map r, hr', hfactor'⟩
  have heq (j : StructuredArrow (Q.obj X) Q) : H.map (π.app j) = π'.app j := by
    obtain ⟨a, ha⟩ := Localization.exists_rightFraction Q W j.hom
    let s : W.Over ⊤ X := ⟨Over.mk a.s, a.hs⟩
    let i := StructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv
    let f : i ⟶ j := StructuredArrow.homMk a.f ha.symm
    have hn := π.naturality f
    have hn' := π'.naturality f
    change 𝟙 Y ≫ π.app j = π.app i ≫ F.map a.f at hn
    change 𝟙 (H.obj Y) ≫ π'.app j = π'.app i ≫ (F ⋙ H).map a.f at hn'
    rw [Category.id_comp] at hn hn'
    rw [hn, hn', H.map_comp, hden s, hden' s]
    rfl
  have hiso : Cone.mk (H.obj Y) π' ≅ H.mapCone (Cone.mk Y π) :=
    Cone.ext (Iso.refl _) (fun j ↦ by simpa using (heq j).symm)
  exact ⟨hlim, preservesLimit_of_preserves_limit_cone hπ
    (IsLimit.ofIsoLimit hπ' hiso)⟩


private theorem pro_absolute
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T)
    (hc : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) Y) :
    H.PreservesRightKanExtension F Q := by
  classical
  have h (X : C) := pro_preserves_at W Q F H X (hc X)
  have : Q.EssSurj := Localization.essSurj Q W
  have : Q.HasPointwiseRightKanExtension F := fun Y ↦
    (Functor.hasPointwiseRightKanExtensionAt_iff_of_iso Q F
      (Q.objObjPreimageIso Y)).1 (h (Q.objPreimage Y)).1
  apply Functor.PreservesRightKanExtension.mk' H F Q
  intro E hE
  have : E.left.IsRightKanExtension E.hom := ⟨⟨hE⟩⟩
  let hp := Functor.isPointwiseRightKanExtensionOfIsRightKanExtension E.left E.hom
  refine ⟨Functor.RightExtension.IsPointwiseRightKanExtension.isUniversal ?_⟩
  intro Y
  have : PreservesLimit (StructuredArrow.proj (Q.obj (Q.objPreimage Y)) Q ⋙ F) H :=
    (h (Q.objPreimage Y)).2
  exact Functor.RightExtension.isPointwiseRightKanExtensionAtOfIso'
    ((Functor.RightExtension.postcompose₂ Q F H).obj E)
    ((hp _).postcompose H) (Q.objObjPreimageIso Y)


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_of_precomp_quotient
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] {H : Type w} [Category.{w'} H]
    (L : HomotopyCategory A (.up ℤ) ⥤ D)
    (G : HomotopyCategory A (.up ℤ) ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G)
    (h : F.IsRightKanExtension
      ((associator (HomotopyCategory.quotient A (.up ℤ)) L F).hom ≫
        whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) α)) :
    F.IsRightKanExtension α := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : ((whiskeringLeft _ _ H).obj q).Full := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Full)
  have : ((whiskeringLeft _ _ H).obj q).Faithful := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Faithful)
  let P := RightExtension.precomp L G q
  have : P.Full := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.full_map₂
  have : P.Faithful := by
    dsimp [P, RightExtension.precomp]
    infer_instance
  let β := (associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  let := h
  exact ⟨⟨IsTerminal.isTerminalOfObj P _
    (IsTerminal.ofIso (F.isUniversalOfIsRightKanExtension β) e.symm)⟩⟩


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {G G' : C ⥤ H} (F : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (α : Q ⋙ F ⟶ G)
    [F.IsRightKanExtension α] :
    F.IsRightKanExtension (whiskerRight i.inv F ≫ α ≫ j.hom) := by
  let P := (rightExtensionEquivalenceOfIso₁ i G).functor ⋙
    (rightExtensionEquivalenceOfIso₂ Q' j).functor
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [P, rightExtensionEquivalenceOfIso₁, rightExtensionEquivalenceOfIso₂])


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_precomp_quotient
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] {H : Type w} [Category.{w'} H]
    (L : HomotopyCategory A (.up ℤ) ⥤ D)
    (G : HomotopyCategory A (.up ℤ) ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G) [F.IsRightKanExtension α] :
    F.IsRightKanExtension
      ((associator (HomotopyCategory.quotient A (.up ℤ)) L F).hom ≫
        whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) α) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : ((whiskeringLeft _ _ H).obj q).Full := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Full)
  have : ((whiskeringLeft _ _ H).obj q).Faithful := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Faithful)
  let P := RightExtension.precomp L G q
  have : P.IsEquivalence := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let β := (associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  exact ⟨⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) e⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A coefficient map descends through a universal counit computed on resolutions.
Source: Stacks Project, derived.tex Tags 06XN and 05SU, and sites-cohomology.tex Tag 06YY.
(blueprint: lem-sbc-derived-coefficient-map-descent).

Proof: Pass to homotopy categories. Quasi-isomorphisms there admit right fractions.
Resolve the source of each denominator by an object of P. These resolutions form
an initial subcategory of the denominator category: resolve a common refinement
and any equalization of two maps. Counit naturality makes the termwise functor
invert every quasi-isomorphism between objects of P. Its denominator pro-diagram
is therefore essentially constant, computed by any such resolution. Applying V
preserves this particular limit, since it is essentially constant. Consequently
the counit whiskered with derived V is still a right Kan extension. Lift the
localized termwise coefficient map into it by its universal property. The Kan
factorization equation is the displayed equation, on every complex. Postcomposition
with a shift equivalence preserves right Kan extensions. Both shifted versions of
the lift have the same factorization equation: the termwise coefficient map,
the counit, and the exact restriction comparison commute with shifts. Uniqueness
of the shifted Kan lift proves the stated shift equality. All choices of resolutions
disappear by uniqueness of this universal lift. -/
theorem exists_derivedCoefficientMap
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (E : A ⥤ B) [E.Additive] (V : B ⥤ A) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (ι : 𝟭 A ⟶ E ⋙ V)
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    [F.CommShift ℤ] [NatTrans.CommShift ε ℤ]
    (P : ObjectProperty (CochainComplex A ℤ))
    (hres : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), P L ∧ QuasiIso p)
    (hε : ∀ K, P K → IsIso (ε.app K)) :
    ∃ η : 𝟭 (DerivedCategory A) ⟶ F ⋙ V.mapDerivedCategory,
      (∀ K : CochainComplex A ℤ,
        η.app (DerivedCategory.Q.obj K) ≫ V.mapDerivedCategory.map (ε.app K) ≫
          V.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app K ≫
            (NatTrans.mapHomologicalComplex ι (.up ℤ)).app K ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ V)) (.up ℤ)).inv.app K)) ∧
      (∀ X : DerivedCategory A,
        η.app ((shiftFunctor _ (1 : ℤ)).obj X) ≫
          ((F ⋙ V.mapDerivedCategory).commShiftIso (1 : ℤ)).hom.app X =
        (shiftFunctor _ (1 : ℤ)).map (η.app X)) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let α₀ := whiskerRight i.hom F ≫ ε ≫ j.inv
  let αpre : q ⋙ (DerivedCategory.Qh ⋙ F) ⟶ q ⋙ H :=
    (associator _ _ _).inv ≫ α₀
  let α : DerivedCategory.Qh ⋙ F ⟶ H :=
    ((whiskeringLeft _ _ _).obj q).preimage αpre
  have hαpre : whiskerLeft q α = αpre :=
    ((whiskeringLeft _ _ _).obj q).map_preimage αpre
  have hα : F.IsRightKanExtension α := by
    apply kan_of_precomp_quotient _ _ _ α
    have := IsLeftDerivedFunctor.isRightKanExtension F ε
      (HomologicalComplex.quasiIso A (.up ℤ))
    have hh := kan_change_iso F i.symm j.symm ε
    have he : (associator q DerivedCategory.Qh F).hom ≫ whiskerLeft q α = α₀ := by
      rw [hαpre]
      simp [αpre]
    rw [he]
    exact hh
  let P' : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, P K ∧ q.obj K = X
  have hres' : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P' ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, p, hL, hp⟩ := hres K
    exact ⟨q.obj L, q.map p, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have hαiso : ∀ X, X ∈ P' → IsIso (α.app X) := by
    rintro X ⟨K, hK, rfl⟩
    have := hε K hK
    have he := NatTrans.congr_app hαpre K
    change α.app (q.obj K) = _ at he
    rw [he]
    dsimp [αpre, α₀]
    simp only [Category.id_comp, isIso_comp_left_iff, MorphismProperty.isomorphisms.iff]
    infer_instance
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P' → Y ∈ P' → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (H.map s) := by
    intro X Y s hX hY hs
    have := hαiso X hX
    have := hαiso Y hY
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh _ _ hs
    have hn := α.naturality s
    rw [← isIso_comp_left_iff (α.app X), ← hn]
    change IsIso (F.map (DerivedCategory.Qh.map s) ≫ α.app Y)
    infer_instance
  have : (HomotopyCategory.quasiIso A (.up ℤ)).HasTwoOutOfThreeProperty :=
    (HomotopyCategory.quasiIso_saturated_triangulated A).2.2.2.2.1
  have habsolute : V.mapDerivedCategory.PreservesRightKanExtension H DerivedCategory.Qh :=
    pro_absolute (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh H
      V.mapDerivedCategory (fun X ↦ by
        obtain ⟨Y, u, hY, _⟩ := resolvingClass_essentialConstancy
          (HomotopyCategory.quasiIso A (.up ℤ)) H P' hres' hinv X
        exact ⟨Y, hY⟩)
  let := hα
  let := habsolute
  let αV := (associator DerivedCategory.Qh F V.mapDerivedCategory).inv ≫
    whiskerRight α V.mapDerivedCategory
  have hαV : (F ⋙ V.mapDerivedCategory).IsRightKanExtension αV := by infer_instance
  let := hαV
  have hpre := kan_precomp_quotient DerivedCategory.Qh (H ⋙ V.mapDerivedCategory)
    (F ⋙ V.mapDerivedCategory) αV
  let k : q ⋙ (H ⋙ V.mapDerivedCategory) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙
        (V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    (associator q H V.mapDerivedCategory).symm ≪≫ isoWhiskerRight j V.mapDerivedCategory ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ V.mapDerivedCategoryFactors
  let δpre := (associator q DerivedCategory.Qh (F ⋙ V.mapDerivedCategory)).hom ≫
    whiskerLeft q αV
  let δ := whiskerRight i.inv (F ⋙ V.mapDerivedCategory) ≫ δpre ≫ k.hom
  have hδ : (F ⋙ V.mapDerivedCategory).IsRightKanExtension δ := by
    let := hpre
    exact kan_change_iso (F ⋙ V.mapDerivedCategory) i k δpre
  have hδapp (K : CochainComplex A ℤ) :
      δ.app K = V.mapDerivedCategory.map (ε.app K) ≫
        V.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
    have he := NatTrans.congr_app hαpre K
    change α.app (q.obj K) = _ at he
    dsimp [δ, δpre, αV, k]
    rw [he]
    dsimp [αpre, α₀]
    simp only [Category.assoc, Category.id_comp]
    erw [Category.id_comp]
    rw [← V.mapDerivedCategory.map_comp_assoc]
    rw [← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]
    rw [← V.mapDerivedCategory.map_comp_assoc]
    rw [Category.assoc, Iso.inv_hom_id_app]
    simp
  let ν : 𝟭 (CochainComplex A ℤ) ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ V.mapHomologicalComplex (.up ℤ) :=
    (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv ≫
      NatTrans.mapHomologicalComplex ι (.up ℤ) ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ V)) (.up ℤ)).inv
  let β : DerivedCategory.Q ⋙ 𝟭 (DerivedCategory A) ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙
        (V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    (DerivedCategory.Q.rightUnitor).hom ≫ DerivedCategory.Q.leftUnitor.inv ≫
      whiskerRight ν DerivedCategory.Q ≫ (associator _ _ _).hom
  let := hδ
  let η := (F ⋙ V.mapDerivedCategory).liftOfIsRightKanExtension δ (𝟭 _) β
  have hη (K : CochainComplex A ℤ) :
      η.app (DerivedCategory.Q.obj K) ≫ δ.app K = DerivedCategory.Q.map (ν.app K) := by
    have he := (F ⋙ V.mapDerivedCategory).liftOfIsRightKanExtension_fac_app
      δ (𝟭 _) β K
    change η.app (DerivedCategory.Q.obj K) ≫ δ.app K = _ at he
    dsimp [β] at he
    erw [Category.id_comp, Category.id_comp, Category.comp_id] at he
    exact he
  refine ⟨η, ?_, ?_⟩
  · intro K
    simpa only [hδapp K, Category.assoc, ν, NatTrans.comp_app] using hη K
  · have hν : NatTrans.CommShift ν ℤ := by
      constructor
      intro n
      ext K k
      simp only [ν, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        HomologicalComplex.comp_f, Functor.commShiftIso_comp_hom_app,
        Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
        Functor.mapHomologicalComplex_map_f, CochainComplex.shiftFunctor_map_f']
      simp only [comp_obj, id_obj, CochainComplex.shiftFunctor_obj_X',
        commShiftIso_id_hom_app, HomologicalComplex.id_f,
        mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
        mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
        Category.id_comp, map_id, Category.comp_id, Category.assoc]
      change ι.app (K.X (k + n)) ≫ 𝟙 _ =
        ι.app (K.X (k + n)) ≫ 𝟙 _ ≫ 𝟙 _
      dsimp only [Functor.mapHomologicalComplex_obj_X, Functor.id_obj, Functor.comp_obj]
      simp only [Category.comp_id]
    let := hν
    have hβ : NatTrans.CommShift β ℤ := by dsimp [β]; infer_instance
    let δ' : DerivedCategory.Q ⋙ (F ⋙ V.mapDerivedCategory) ⟶
        E.mapHomologicalComplex (.up ℤ) ⋙
          (V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
      (associator DerivedCategory.Q F V.mapDerivedCategory).inv ≫
        whiskerRight ε V.mapDerivedCategory ≫ (associator _ _ _).hom ≫
        whiskerLeft (E.mapHomologicalComplex (.up ℤ)) V.mapDerivedCategoryFactors.hom
    have hδeq : δ = δ' := by
      ext K
      simpa [δ'] using hδapp K
    have hδshift : NatTrans.CommShift δ ℤ := by
      rw [hδeq]
      dsimp [δ']
      infer_instance
    let := hδshift
    let := hβ
    have hηshift : NatTrans.CommShift η ℤ := kanMap_commShift _ _ _ δ _ β η
      ((F ⋙ V.mapDerivedCategory).liftOfIsRightKanExtension_fac δ (𝟭 _) β)
    let := hηshift
    intro X
    simpa using (NatTrans.shift_app_comm η (1 : ℤ) X).symm

end CategoryTheory.Functor
