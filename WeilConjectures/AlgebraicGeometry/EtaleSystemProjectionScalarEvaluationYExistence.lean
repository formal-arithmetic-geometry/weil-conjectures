/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionBasicData
import all WeilConjectures.AlgebraicGeometry.EtaleBrownLevelRealizationData
import all WeilConjectures.AlgebraicGeometry.ScalarDataExistence
import WeilConjectures.AlgebraicGeometry.ScalarEvaluationTransposeExistence
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Target scalar evaluation comparison existence for normalized etale systems

Source: Zheng, Construction 4.1, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open scoped CategoryTheory.TwoSquare
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemProjection

private def toScalarData {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} {φ : R ⟶ S}
    (x : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1} φ) :
    ScalarData.{u + 1, u, u + 1} φ :=
  { model := x.model
    ordinaryAdjunction := x.ordinaryAdj
    unit_section := by
      intro M U z
      rw [x.unit_normalized]
      dsimp only [SheafOfModules.systemModelTmul]
      rw [one_smul]
      have hh : eqToHom (x.model.obj_eq M).symm ≫ eqToHom (x.model.obj_eq M) =
          𝟙 _ := by simp
      exact congrArg (fun f ↦ f.val.app U (extensionUnit φ M U z)) hh
    adjunction := x.adjunction
    transpose_model := by
      intro P Q _hP f
      rw [x.transpose]
      simp }

private def ordinaryComparison
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (G : A ⥤ B) (K : B ⥤ C) (H : D ⥤ E) (L : E ⥤ F)
    (R : A ⥤ D) (S : B ⥤ E) (T : C ⥤ F)
    (G02 : A ⥤ C) (H02 : D ⥤ F)
    (δ : R ⋙ H ≅ G ⋙ S) (κ : S ⋙ L ≅ K ⋙ T)
    (cg : G02 ≅ G ⋙ K) (ch : H02 ≅ H ⋙ L) : R ⋙ H02 ≅ G02 ⋙ T :=
  Functor.isoWhiskerLeft R ch ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight δ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ κ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight cg.symm T

private theorem ordinaryComparison_fac
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (G : A ⥤ B) (K : B ⥤ C) (H : D ⥤ E) (L : E ⥤ F)
    (R : A ⥤ D) (S : B ⥤ E) (T : C ⥤ F)
    (G02 : A ⥤ C) (H02 : D ⥤ F)
    (δ : R ⋙ H ≅ G ⋙ S) (κ : S ⋙ L ≅ K ⋙ T)
    (cg : G02 ≅ G ⋙ K) (ch : H02 ≅ H ⋙ L) (M : A) :
    (ordinaryComparison G K H L R S T G02 H02 δ κ cg ch).hom.app M ≫
        T.map (cg.hom.app M) =
      ch.hom.app (R.obj M) ≫ L.map (δ.hom.app M) ≫ κ.hom.app (G.obj M) := by
  dsimp only [ordinaryComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj]
  simp [Category.assoc, ← T.map_comp]

private theorem pastedRestriction
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
    (G : A ⥤ B) (K : B ⥤ C) (H : D ⥤ E) (L : E ⥤ F)
    (R : A ⥤ D) (S : B ⥤ E) (T : C ⥤ F)
    (G02 : A ⥤ C) (H02 : D ⥤ F)
    [G.Additive] [K.Additive] [H.Additive] [L.Additive]
    [R.Additive] [S.Additive] [T.Additive] [G02.Additive] [H02.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits G02] [PreservesFiniteColimits G02]
    [PreservesFiniteLimits H02] [PreservesFiniteColimits H02]
    [PreservesFiniteLimits (G ⋙ K)] [PreservesFiniteColimits (G ⋙ K)]
    [PreservesFiniteLimits (H ⋙ L)] [PreservesFiniteColimits (H ⋙ L)]
    (δ : R ⋙ H ≅ G ⋙ S) (κ : S ⋙ L ≅ K ⋙ T)
    (ordinary : R ⋙ H02 ≅ G02 ⋙ T) (cg : G02 ≅ G ⋙ K) (ch : H02 ≅ H ⋙ L)
    (ho : ∀ M, ordinary.hom.app M ≫ T.map (cg.hom.app M) =
      ch.hom.app (R.obj M) ≫ L.map (δ.hom.app M) ≫ κ.hom.app (G.obj M)) :
    let g := Functor.mapDerivedCategoryNatIso ch ≪≫ Functor.mapDerivedCategoryCompIso H L
    let h := Functor.mapDerivedCategoryNatIso cg ≪≫ Functor.mapDerivedCategoryCompIso G K
    let δD := Functor.mapDerivedCategorySquareIso δ
    let κD := Functor.mapDerivedCategorySquareIso κ
    Functor.whiskerLeft R.mapDerivedCategory g.hom ≫
        ((TwoSquare.mk _ _ _ _ δD.hom) ≫ᵥ
          (TwoSquare.mk _ _ _ _ κD.hom)).natTrans ≫
        Functor.whiskerRight h.inv T.mapDerivedCategory =
      (Functor.mapDerivedCategorySquareIso ordinary).hom := by
  dsimp only
  apply NatTrans.ext
  funext M
  apply (cancel_mono
    (T.mapDerivedCategory.map
      ((Functor.mapDerivedCategoryNatIso cg ≪≫
        Functor.mapDerivedCategoryCompIso G K).hom.app M))).mp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  have hd := Functor.exactSquare_comp_inverse G K G02 H L H02 R S T
    δ κ ordinary cg ch ho M
  simpa only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    TwoSquare.mk, TwoSquare.natTrans, CategoryTheory.Functor.map_id,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc] using hd.symm

set_option maxHeartbeats 1600000 in
-- Transporting the exact-evaluation squares compares large derived-functor types.
/-- The normalized scalar evaluation comparison exists on the target scheme.
Source: Zheng Lemma 5.16; Stacks 0GL6.
(blueprint: lem-pur-etale-system-projection-scalar-evaluation-y-existence).

Proof: The ordinary restriction-of-scalars comparison is identity on sections. Its
canonical derived localization and the normalized scalar adjunction mate give the
specified scalar evaluation comparison.
-/
theorem scalarEvaluationY_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :
    Nonempty (ScalarEvaluation Y a (b.scalarY a) n
      (b.evaluationY B n) (b.evaluationY C n)) := by
  classical
  let eb := b.evaluationY B n
  let ec := b.evaluationY C n
  let := eb.additive
  let := eb.limits
  let := eb.colimits
  let := ec.additive
  let := ec.limits
  let := ec.colimits
  let J := Y.smallEtaleTopology
  let α := fun k ↦ (constantSheaf J CommRingCat.{u + 1}).map (a.app (op k))
  have hα : ∀ k, α (k + 1) ≫ transitions Y C.rings k = transitions Y B.rings k ≫ α k := by
    intro k
    dsimp [α, transitions]
    rw [← Functor.map_comp, ← Functor.map_comp]
    have hn := (a.naturality (homOfLE (Nat.le_succ k)).op).symm
    exact congrArg (fun h ↦ (constantSheaf J CommRingCat.{u + 1}).map h) hn
  let S : ScalarData.{u + 1, u, u + 1} (ringMap Y a) := toScalarData (b.scalarY a)
  let L : ∀ k, ScalarData.{u + 1, u, u + 1} (α k) := fun k ↦
    Classical.choice (scalarData_nonempty.{u + 1, u, u + 1} J (α k))
  obtain ⟨E⟩ := semilinearScalarEvaluationTranspose.{u + 1, u, u + 1} J
    (coefficients Y B.rings) (transitions Y B.rings)
    (coefficients Y C.rings) (transitions Y C.rings) α hα S L
  let δ := (restrictionEvaluation_existsUnique J
    (coefficients Y B.rings) (transitions Y B.rings)
    (coefficients Y C.rings) (transitions Y C.rings) α hα n).exists.choose
  let κ := brownGenericRestriction Y (B.rings.obj (op n)) (C.rings.obj (op n)) (a.app (op n))
  let G := evaluation J (coefficients Y B.rings) (transitions Y B.rings) n
  let H := evaluation J (coefficients Y C.rings) (transitions Y C.rings) n
  let F := constantModule Y (B.rings.obj (op n))
  let K := constantModule Y (C.rings.obj (op n))
  let cg : level Y C.rings n ≅ H ⋙ K := Iso.refl _
  let ch : level Y B.rings n ≅ G ⋙ F := Iso.refl _
  let ordinary := ordinaryComparison H K G F
    (res (ringMap Y a)) (res (α n))
    (Sheaf.restrictScalars J (a.app (op n)).hom)
    (level Y C.rings n) (level Y B.rings n) δ κ cg ch
  have ho := ordinaryComparison_fac H K G F
    (res (ringMap Y a)) (res (α n))
    (Sheaf.restrictScalars J (a.app (op n)).hom)
    (level Y C.rings n) (level Y B.rings n) δ κ cg ch
  let : F.IsEquivalence := brownConstantEquivalence Y _
  let : K.IsEquivalence := brownConstantEquivalence Y _
  let : F.Additive := brownConstantAdditive Y _
  let : K.Additive := brownConstantAdditive Y _
  let δD := Functor.mapDerivedCategorySquareIso δ
  let κD := Functor.mapDerivedCategorySquareIso κ
  let a₁ := (b.scalarY a).adjunction
  let a₂ := (L n).adjunction
  let a₃ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars J (a.app (op n)).hom)
  let i : (b.scalarY a).model.T ⋙ H.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ (L n).model.T := E.evaluation n
  have hi : i.inv = ((mateEquiv a₁ a₂).symm
      (TwoSquare.mk _ _ _ _ δD.hom)).natTrans := by
    ext M
    apply (a₂.homEquiv _ _).injective
    have h₁ := E.transpose_evaluation n M (S.T.obj M) (𝟙 _)
    have h₂ := adjunctionMate_transpose a₁ a₂
      (TwoSquare.mk _ _ _ _ δD.hom) M (S.T.obj M) (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h₁ h₂
    exact h₁.symm.trans h₂.symm
  let j := brownInverseMateIso a₂ a₃ κD
  let x := TwoSquare.mk _ _ _ _ i.inv
  let y := TwoSquare.mk _ _ _ _ j.inv
  have hx : mateEquiv a₁ a₂ x = TwoSquare.mk _ _ _ _ δD.hom := by
    dsimp only [x]
    rw [hi]
    exact (mateEquiv a₁ a₂).apply_symm_apply _
  have hy : mateEquiv a₂ a₃ y = TwoSquare.mk _ _ _ _ κD.hom := by
    exact (mateEquiv a₂ a₃).apply_symm_apply _
  let z := x ≫ₕ y
  have hz : mateEquiv a₁ a₃ z =
      (TwoSquare.mk _ _ _ _ δD.hom) ≫ᵥ (TwoSquare.mk _ _ _ _ κD.hom) := by
    rw [mateEquiv_vcomp, hx, hy]
  let g : eb.E ≅ G.mapDerivedCategory ⋙ F.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso ch ≪≫
      Functor.mapDerivedCategoryCompIso G F
  let h : ec.E ≅ H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso cg ≪≫
      Functor.mapDerivedCategoryCompIso H K
  let total := Functor.mapDerivedCategorySquareIso ordinary
  let v : eb.E ⋙ scalarExtension (a.app (op n)).hom Y ⟶
      (b.scalarY a).model.T ⋙ ec.E :=
    Functor.whiskerRight g.hom _ ≫ z.natTrans ≫ Functor.whiskerLeft _ h.inv
  have hv : IsIso v := by
    dsimp only [v, z, x, y, TwoSquare.hComp]
    infer_instance
  have hm : mateEquiv a₁ a₃ (TwoSquare.mk _ _ _ _ v) =
      TwoSquare.mk _ _ _ _ total.hom := by
    dsimp only [v]
    erw [← Category.assoc, mateEquiv_comp_whiskerLeft,
      mateEquiv_whiskerRight_comp, hz]
    have hp :
        Functor.whiskerLeft (restriction Y a) g.hom ≫
            ((TwoSquare.mk _ _ _ _ δD.hom) ≫ᵥ
              (TwoSquare.mk _ _ _ _ κD.hom)).natTrans ≫
            Functor.whiskerRight h.inv
              (Sheaf.derivedRestrictScalars J (a.app (op n)).hom) = total.hom := by
      exact pastedRestriction H K G F
        (res (ringMap Y a)) (res (α n))
        (Sheaf.restrictScalars J (a.app (op n)).hom)
        (level Y C.rings n) (level Y B.rings n) δ κ ordinary cg ch ho
    apply TwoSquare.ext
    intro M
    simpa only [TwoSquare.natTrans, TwoSquare.mk, Category.assoc] using
      NatTrans.congr_app hp M
  refine ⟨{ ordinary := ordinary
            sections := ?_
            restriction := total
            restriction_termwise := rfl
            iso := (@asIso _ _ _ _ v hv).symm
            mate := ?_ }⟩
  · intro M U x
    have hd := (restrictionEvaluation_existsUnique J
      (coefficients Y B.rings) (transitions Y B.rings)
      (coefficients Y C.rings) (transitions Y C.rings) α hα n).exists.choose_spec M U
    have hx := congrFun (eq_of_heq hd) x
    exact heq_of_eq hx
  · have hh := congrArg (mateEquiv a₁ a₃).symm hm
    rw [Equiv.symm_apply_apply] at hh
    exact congrArg TwoSquare.natTrans hh

end AlgebraicGeometry.Etale.SystemProjection
