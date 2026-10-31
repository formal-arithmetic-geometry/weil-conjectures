/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PostnikovAdditiveExactCoupleData
import all WeilConjectures.CategoryTheory.PostnikovAdditiveExactCoupleData
import all WeilConjectures.CategoryTheory.PostnikovFiniteCutoffAbutment
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import all Mathlib.CategoryTheory.Triangulated.Basic
import all Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # The normalized initial Postnikov exact couple

Source: Stacks Project, Derived Categories, Tag 08J5; Homology, Tags 011Q and 0AMJ.

Construct the canonical layer comparison from homology full faithfulness, then use the
three exact positions of the shifted truncation triangle to form the initial couple.
-/

@[expose] public section

set_option autoImplicit false

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

private noncomputable def layerHomologyIso (q : ℤ) (L : DerivedCategory A) :
    (homologyFunctor A q).obj ((TStructure.t.truncGELT q (q + 1)).obj L) ≅
      (homologyFunctor A q).obj L :=
  have := isIso_homologyFunctor_map_truncGEπ_app
    ((TStructure.t.truncLT (q + 1)).obj L) q q le_rfl
  have := isIso_homologyFunctor_map_truncLTι_app L (q + 1) q (by omega)
  (asIso ((homologyFunctor A q).map
    ((TStructure.t.truncGEπ q).app ((TStructure.t.truncLT (q + 1)).obj L)))).symm ≪≫
      asIso ((homologyFunctor A q).map ((TStructure.t.truncLTι (q + 1)).app L))

private theorem layerHomologyIso_natural (q : ℤ) {L M : DerivedCategory A} (u : L ⟶ M) :
    (homologyFunctor A q).map ((TStructure.t.truncGELT q (q + 1)).map u) ≫
        (layerHomologyIso q M).hom =
      (layerHomologyIso q L).hom ≫ (homologyFunctor A q).map u := by
  have := isIso_homologyFunctor_map_truncGEπ_app
    ((TStructure.t.truncLT (q + 1)).obj M) q q le_rfl
  have hπ := congrArg (homologyFunctor A q).map
    ((TStructure.t.truncGEπ q).naturality ((TStructure.t.truncLT (q + 1)).map u))
  have hι := congrArg (homologyFunctor A q).map
    ((TStructure.t.truncLTι (q + 1)).naturality u)
  simp only [Functor.map_comp] at hπ hι
  have := isIso_homologyFunctor_map_truncGEπ_app
    ((TStructure.t.truncLT (q + 1)).obj L) q q le_rfl
  apply (cancel_epi ((homologyFunctor A q).map
    ((TStructure.t.truncGEπ q).app ((TStructure.t.truncLT (q + 1)).obj L)))).mp
  dsimp only [layerHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  change (homologyFunctor A q).map _ ≫
    ((homologyFunctor A q).map ((TStructure.t.truncGE q).map
      ((TStructure.t.truncLT (q + 1)).map u)) ≫ _) = _
  rw [← Category.assoc, ← hπ, Category.assoc, IsIso.hom_inv_id_assoc]
  simpa only [Functor.id_map, Category.assoc, IsIso.hom_inv_id_assoc] using hι

private instance layer_isLE (q : ℤ) (L : DerivedCategory A) :
    ((TStructure.t.truncGELT q (q + 1)).obj L).IsLE q := by
  simpa only [add_sub_cancel_right] using
    (inferInstance : ((TStructure.t.truncGELT q (q + 1)).obj L).IsLE (q + 1 - 1))

private instance singleLayer_isLE (q : ℤ) (L : DerivedCategory A) :
    ((postnikovLayer q).obj L).IsLE q := by
  change ((singleFunctor A q).obj _).IsLE q
  infer_instance

private instance singleLayer_isGE (q : ℤ) (L : DerivedCategory A) :
    ((postnikovLayer q).obj L).IsGE q := by
  change ((singleFunctor A q).obj _).IsGE q
  infer_instance

private noncomputable def layerMap (q : ℤ) (L : DerivedCategory A) :
    (TStructure.t.truncGELT q (q + 1)).obj L ⟶ (postnikovLayer q).obj L :=
  (homologyFunctor_map_bijective_of_isLE_of_isGE q).surjective
    ((layerHomologyIso q L).hom ≫
      (singleFunctorCompHomologyFunctorIso A q).inv.app ((homologyFunctor A q).obj L))
    |>.choose

private theorem layerMap_eq (q : ℤ) (L : DerivedCategory A) :
    (homologyFunctor A q).map (layerMap q L) =
      (layerHomologyIso q L).hom ≫
        (singleFunctorCompHomologyFunctorIso A q).inv.app ((homologyFunctor A q).obj L) :=
  (homologyFunctor_map_bijective_of_isLE_of_isGE q).surjective _ |>.choose_spec

private theorem layerMap_isIso (q : ℤ) (L : DerivedCategory A) : IsIso (layerMap q L) := by
  have h : IsIso ((homologyFunctor A q).map (layerMap q L)) := by
    rw [layerMap_eq]
    infer_instance
  obtain ⟨g, hg⟩ := (homologyFunctor_map_bijective_of_isLE_of_isGE
    (X := (postnikovLayer q).obj L)
    (Y := (TStructure.t.truncGELT q (q + 1)).obj L) q).surjective
      (inv ((homologyFunctor A q).map (layerMap q L)))
  refine ⟨g, ?_, ?_⟩
  · apply (homologyFunctor_map_bijective_of_isLE_of_isGE q).injective
    simp [Functor.map_comp, hg]
  · apply (homologyFunctor_map_bijective_of_isLE_of_isGE q).injective
    simp [Functor.map_comp, hg]

private noncomputable def layerComparison (q : ℤ) :
    TStructure.t.truncGELT q (q + 1) ≅ postnikovLayer (A := A) q := by
  let τ : TStructure.t.truncGELT q (q + 1) ⟶ postnikovLayer (A := A) q :=
    { app := layerMap q
      naturality := fun L M u ↦ by
        apply (homologyFunctor_map_bijective_of_isLE_of_isGE q).injective
        simp only [Functor.map_comp, layerMap_eq, Category.assoc]
        rw [← Category.assoc, layerHomologyIso_natural, Category.assoc]
        congr 1
        exact (singleFunctorCompHomologyFunctorIso A q).inv.naturality
          ((homologyFunctor A q).map u) }
  have : ∀ L, IsIso (τ.app L) := layerMap_isIso q
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

private noncomputable def canonicalTower : PostnikovTriangleData A where
  layerIso := layerComparison
  layer_normalized q L := by
    change (homologyFunctor A q).map
      ((TStructure.t.truncGEπ q).app ((TStructure.t.truncLT (q + 1)).obj L) ≫
        layerMap q L) ≫ _ = _
    rw [Functor.map_comp, layerMap_eq]
    dsimp only [layerHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
    simp only [Category.assoc, Iso.inv_hom_id_app, IsIso.hom_inv_id_assoc]
    exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem exact_transport
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : B} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (w : a ≫ b = 0) (h : (ShortComplex.mk a b w).Exact)
    {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (h₁ : e₁.hom ≫ a' = a ≫ e₂.hom)
    (h₂ : e₂.hom ≫ b' = b ≫ e₃.hom) :
    ∃ w' : a' ≫ b' = 0, (ShortComplex.mk _ _ w').Exact := by
  have w' : a' ≫ b' = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, h₁, Category.assoc, h₂,
      ← Category.assoc, w, zero_comp, comp_zero]
  refine ⟨w', ShortComplex.exact_of_iso ?_ h⟩
  exact ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂

private theorem postnikov_exact_alpha (T : DerivedCategory A ⥤ B) [T.IsHomological]
    (ρ p q : ℤ) (L : DerivedCategory A) :
    imageSubobject (postnikovF T ρ p q L) =
      kernelSubobject (postnikovAlpha T ρ (p + 2) (q - 1) L) := by
  let U := ((TStructure.t.triangleLTLTGELT q (q + 1) (by omega)).obj L)
  have hU := TStructure.t.triangleLTLTGELT_distinguished q (q + 1) (by omega) L
  let S : T.ShiftSequence ℤ := Functor.ShiftSequence.tautological T ℤ
  let n := p + q - ρ
  let n' := p + 2 + (q - 1) - ρ
  let a := T.homologySequenceδ U n n' (by dsimp [n, n']; omega)
  let b := (postnikovValue T n').map U.mor₁
  have w : a ≫ b = 0 := T.homologySequenceδ_comp U hU n n' (by dsimp [n, n']; omega)
  have h : (ShortComplex.mk a b w).Exact :=
    T.homologySequence_exact₁ U hU n n' (by dsimp [n, n']; omega)
  obtain ⟨w', h'⟩ := exact_transport a b w h
    (a' := postnikovF T ρ p q L) (b' := postnikovAlpha T ρ (p + 2) (q - 1) L)
    (Iso.refl _) (eqToIso (congrArg (fun k : ℤ ↦
      (postnikovValue T n').obj ((TStructure.t.truncLT k).obj L))
      (show q = q - 1 + 1 by omega)))
    (eqToIso (congrArg (fun kn : ℤ × ℤ ↦
      (postnikovValue T kn.2).obj ((TStructure.t.truncLT kn.1).obj L))
      (show (q + 1, n') =
        (q - 1 + 1 + 1, p + 2 - 1 + (q - 1 + 1) - ρ) by
        dsimp [n']; ext <;> omega))) (by
      simp only [Iso.refl_hom, Category.id_comp, eqToIso.hom]
      change postnikovF T ρ p q L = a ≫ eqToHom _
      change (T.map (_ ≫ _) ≫ eqToHom _) =
        (T.map _ ≫ (𝟙 _ ≫ T.map _)) ≫ eqToHom _
      simp only [Category.id_comp, Functor.map_comp, Iso.symm_hom]
      rfl) (by
      dsimp only [eqToIso.hom]
      change eqToHom (congrArg (fun k : ℤ ↦
          (postnikovValue T n').obj ((TStructure.t.truncLT k).obj L))
          (show q = q - 1 + 1 by omega)) ≫
        ((postnikovValue T n').map
          ((TStructure.t.natTransTruncLTOfLE (q - 1 + 1)
            (q - 1 + 1 + 1) (by omega)).app L) ≫
          eqToHom (congrArg (fun d : ℤ ↦ (postnikovValue T d).obj
            ((TStructure.t.truncLT (q - 1 + 1 + 1)).obj L))
            (show n' = p + 2 - 1 + (q - 1 + 1) - ρ by dsimp [n']; omega))) =
        (postnikovValue T n').map
          ((TStructure.t.natTransTruncLTOfLE q (q + 1) (by omega)).app L) ≫
          eqToHom (congrArg (fun kn : ℤ × ℤ ↦
            (postnikovValue T kn.2).obj ((TStructure.t.truncLT kn.1).obj L))
            (show (q + 1, n') =
              (q - 1 + 1 + 1, p + 2 - 1 + (q - 1 + 1) - ρ) by
                dsimp [n']; ext <;> omega))
      rw [← Category.assoc, ← eqToHom_naturality
        (fun k : ℤ ↦ (postnikovValue T n').map
          ((TStructure.t.natTransTruncLTOfLE k (k + 1) (by omega)).app L))
        (show q = q - 1 + 1 by omega), Category.assoc, eqToHom_trans])
  exact (ShortComplex.exact_iff_image_eq_kernel _).mp h'
private theorem postnikov_exact_f (T : DerivedCategory A ⥤ B) [T.IsHomological]
    (ρ p q : ℤ) (L : DerivedCategory A) :
    imageSubobject (postnikovG T ρ p q L) =
      kernelSubobject (postnikovF T ρ p q L) := by
  let U := ((TStructure.t.triangleLTLTGELT q (q + 1) (by omega)).obj L)
  have hU := TStructure.t.triangleLTLTGELT_distinguished q (q + 1) (by omega) L
  let S : T.ShiftSequence ℤ := Functor.ShiftSequence.tautological T ℤ
  have h := T.homologySequence_exact₂ U.rotate (rot_of_distTriang U hU) (p + q - ρ)
  have w := T.homologySequence_comp U.rotate (rot_of_distTriang U hU) (p + q - ρ)
  change postnikovG T ρ p q L ≫ T.map (U.mor₃⟦p + q - ρ⟧') = 0 at w
  have h' : (ShortComplex.mk (postnikovG T ρ p q L)
      (T.map (U.mor₃⟦p + q - ρ⟧')) w).Exact := h
  have he := (ShortComplex.exact_iff_image_eq_kernel _).mp h'
  simpa only [postnikovF, Functor.map_comp, kernelSubobject_comp_mono] using he
private theorem postnikov_exact_g (T : DerivedCategory A ⥤ B) [T.IsHomological]
    (ρ p q : ℤ) (L : DerivedCategory A) :
    imageSubobject (postnikovAlpha T ρ p q L) =
      kernelSubobject (postnikovG T ρ (p - 1) (q + 1) L) := by
  let U := ((TStructure.t.triangleLTLTGELT (q + 1) (q + 1 + 1) (by omega)).obj L)
  have hU := TStructure.t.triangleLTLTGELT_distinguished (q + 1) (q + 1 + 1)
    (by omega) L
  let S : T.ShiftSequence ℤ := Functor.ShiftSequence.tautological T ℤ
  let n := p + q - ρ
  have h := T.homologySequence_exact₂ U hU n
  have w := T.homologySequence_comp U hU n
  obtain ⟨w', h'⟩ := exact_transport _ _ w h
    (a' := postnikovAlpha T ρ p q L) (b' := postnikovG T ρ (p - 1) (q + 1) L)
    (Iso.refl _) (eqToIso (congrArg (fun n : ℤ ↦
      (postnikovValue T n).obj ((TStructure.t.truncLE (q + 1)).obj L))
      (show p + q - ρ = p - 1 + (q + 1) - ρ by omega)))
    (eqToIso (congrArg (fun n : ℤ ↦
      (postnikovValue T n).obj
        ((TStructure.t.truncGELT (q + 1) (q + 1 + 1)).obj L))
      (show p + q - ρ = p - 1 + (q + 1) - ρ by omega)))
    (by simp only [Iso.refl_hom, Category.id_comp]; rfl) (by
      dsimp only [eqToIso.hom, postnikovG]
      exact (eqToHom_naturality (fun n : ℤ ↦ (postnikovValue T n).map U.mor₂)
        (show p + q - ρ = p - 1 + (q + 1) - ρ by omega)).symm)
  exact (ShortComplex.exact_iff_image_eq_kernel _).mp h'

private theorem zero_of_image_eq_kernel {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : imageSubobject f = kernelSubobject g) : f ≫ g = 0 := by
  apply (kernelSubobject_factors_iff g f).mp
  rw [← h]
  simpa only [Category.id_comp] using imageSubobject_factors_comp_self f (𝟙 _)

private theorem postnikov_exact_f_transport (T : DerivedCategory A ⥤ B)
    [T.IsHomological] (ρ p q p' q' : ℤ) (hp : p = p') (hq : q = q')
    (L : DerivedCategory A) :
    imageSubobject (postnikovG T ρ p q L ≫
      eqToHom (congrArg₂ (fun p q : ℤ ↦ (postnikovE T ρ p q).obj L) hp hq)) =
      kernelSubobject (postnikovF T ρ p' q' L) := by
  subst p'
  subst q'
  simpa only [eqToHom_refl, Category.comp_id] using postnikov_exact_f T ρ p q L

private noncomputable def canonicalCouple (T : DerivedCategory A ⥤ B) [T.IsHomological]
    (ρ : ℤ) (L : DerivedCategory A) : BigradedExactCouple B 0 where
  D p q := (postnikovD T ρ p q).obj L
  E p q := (postnikovE T ρ p q).obj L
  alpha p q := postnikovAlpha T ρ p q L
  f p q := postnikovF T ρ p q L
  g p q := postnikovG T ρ p q L ≫
    eqToHom (congrArg₂ (fun p q : ℤ ↦ (postnikovE T ρ p q).obj L)
      (by omega) (by omega))
  alpha_f_zero p q := zero_of_image_eq_kernel _ _ (postnikov_exact_alpha T ρ p q L)
  f_g_zero p q := zero_of_image_eq_kernel _ _
    (postnikov_exact_f_transport T ρ p q _ _ (by omega) (by omega) L)
  g_alpha_zero p q := by
    rw [← Category.assoc, zero_of_image_eq_kernel _ _ (postnikov_exact_g T ρ p q L),
      zero_comp]
  exact_alpha p q := postnikov_exact_alpha T ρ p q L
  exact_f p q := postnikov_exact_f_transport T ρ p q _ _ (by omega) (by omega) L
  exact_g p q := by
    rw [kernelSubobject_comp_mono]
    exact postnikov_exact_g T ρ p q L

private noncomputable def initialComparison (T : DerivedCategory A ⥤ B)
    (ρ p q : ℤ) : postnikovE T ρ p q ≅
      homologyFunctor A q ⋙ singleFunctor A 0 ⋙
        shiftFunctor (DerivedCategory A) (p - ρ) ⋙ T :=
  Functor.isoWhiskerRight (layerComparison q) (postnikovValue T (p + q - ρ)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (homologyFunctor A q)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((singleFunctors A).shiftIso (p + q - ρ) (ρ - p) q (by omega) ≪≫
            ((singleFunctors A).shiftIso (p - ρ) (ρ - p) 0 (by omega)).symm) T ≪≫
        Functor.associator _ _ _)

/-- The canonical truncation maps give the initial exact couple, with the normalized
cohomology-layer and shift comparisons.

Source: Stacks Project, Derived Categories, Tag 08J5; Homology, Tags 011Q and 0AMJ
(blueprint: lem-per-postnikov-canonical-exact-couple).

Proof: Identify the single-degree layer with the single-term embedding by the unique
map inducing the truncation cohomology comparison. Full faithfulness of homology on
the shifted heart proves naturality and invertibility and fixes the normalization.
Apply the three exact positions of the shifted homology sequence of the canonical
successive-truncation triangle. Transport its endpoints along the equalities of total
degrees. These prove the three image/kernel equalities and the zero composites.
Use these maps and objects verbatim for the initial couple, so its comparison squares
are identities. The coherent single-functor shift isomorphisms give the E2 comparison. -/
theorem exists_postnikov_canonical_exact_couple
    (T : DerivedCategory A ⥤ B) [T.IsHomological] : Nonempty (PostnikovCoupleData T) := by
  classical
  refine ⟨{ tower := canonicalTower
            couple := canonicalCouple T
            dIso := fun _ _ _ _ ↦ Iso.refl _
            eIso := fun _ _ _ _ ↦ Iso.refl _
            alpha_eq := ?_
            g_eq := ?_
            f_eq := ?_
            initialPageIso := initialComparison T
            initialPageIso_eq := ?_ }⟩
  · intro ρ L p q
    simp only [canonicalCouple, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · intro ρ L p q
    simp only [BigradedExactCouple.initialG, canonicalCouple, Iso.refl_hom,
      Category.comp_id, Category.id_comp, Category.assoc, eqToHom_trans, eqToHom_refl]
  · intro ρ L p q
    simp only [canonicalCouple, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · intro ρ p q L
    simp [initialComparison, canonicalTower, postnikovLayer, Functor.map_comp]

end DerivedCategory
