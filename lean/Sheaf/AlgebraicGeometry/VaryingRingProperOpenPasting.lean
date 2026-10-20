/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.SemilinearDerivedSections
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

/-!
# Proper/open projection and pasting for varying coefficient rings

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7D, open-immersion cases; the
agent-formulated varying-ring extension extracted from the blueprint's local-pairs
construction (blueprint: lem-sp-varying-ring-proper-open-pasting).

Every map below lives on the ordinary derived category of strict semilinear systems.
The ordinary system maps and their two pasting equations are stated separately, so
these equalities precede evaluation. No invertibility of gamma on arbitrary inputs
is asserted.

## Main statements

- `modulePi_components`: identity on the image and zero on the complement.
- `moduleAlpha_vertical`, `moduleAlpha_horizontal`: intrinsic system pasting.
- `alpha_vertical`, `alpha_horizontal`, `properOpenPasting`: derived pasting laws.
- `alpha_identities`, `gamma_identities`, `gamma_evaluation`: normalization and evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

private theorem mate_whisker
    {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (a : G ⋙ L₂ ⟶ L₁ ⋙ H) (t : G' ⟶ G) (b : H ⟶ H') :
    mateEquiv adj₁ adj₂
        (Functor.whiskerRight t L₂ ≫ a ≫ Functor.whiskerLeft L₁ b) =
      Functor.whiskerLeft R₁ t ≫ mateEquiv adj₁ adj₂ a ≫
        Functor.whiskerRight b R₂ := by
  apply TwoSquare.ext
  intro X
  dsimp [mateEquiv, TwoSquare.natTrans]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have ht := adj₂.unit.naturality (t.app (R₁.obj X))
  dsimp at ht
  rw [← reassoc_of% ht]
  slice_lhs 4 5 => rw [← R₂.map_comp, ← b.naturality, R₂.map_comp]




section DerivedMaps

variable {A₀ B₁ B₂ C₀ : Type*}
  [Category A₀] [Category B₁] [Category B₂] [Category C₀]
  [Abelian A₀] [Abelian B₁] [Abelian B₂] [Abelian C₀]
  [HasDerivedCategory A₀] [HasDerivedCategory B₁]
  [HasDerivedCategory B₂] [HasDerivedCategory C₀]
  (F₁ : A₀ ⥤ B₁) (F₂ : B₁ ⥤ C₀) (G₁ : A₀ ⥤ B₂) (G₂ : B₂ ⥤ C₀)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

private def derivedSquare (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F₁ F₂).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso A₀ (.up ℤ)) _ _
      (F₁ ⋙ F₂).mapDerivedCategory (G₁ ⋙ G₂).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso G₁ G₂).hom

set_option backward.isDefEq.respectTransparency false in
private theorem derivedSquare_fac (t : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    (K : CochainComplex A₀ ℤ) :
    (derivedSquare F₁ F₂ G₁ G₂ t).app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) := by
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ K
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ K
  dsimp only [derivedSquare, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, hG, Localization.liftNatTrans_app]
  change _ ≫ (_ ≫ _ ≫ (G₁ ⋙ G₂).mapDerivedCategoryFactors.inv.app K) ≫
      (G₁ ⋙ G₂).mapDerivedCategoryFactors.hom.app K = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change (Functor.mapDerivedCategoryCompIso F₁ F₂).inv.app (DerivedCategory.Q.obj K) ≫
    (F₁ ⋙ F₂).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K) = _
  rw [← hF]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

variable (F₀ : A₀ ⥤ C₀) [F₀.Additive]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]

private theorem derivedTriangle_fac (e : F₀ ≅ F₁ ⋙ F₂) (K : CochainComplex A₀ ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryCompIso F₁ F₂).hom.app (DerivedCategory.Q.obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₀.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]

private theorem derivedComp_fac (e : F₁ ⋙ F₂ ≅ F₀) (K : CochainComplex A₀ ℤ) :
    ((Functor.mapDerivedCategoryCompIso F₁ F₂).symm ≪≫
        Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K) ≫
        F₀.mapDerivedCategoryFactors.hom.app K =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ K]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end DerivedMaps

attribute [local irreducible] derivedSquare Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategory DerivedCategory.Q

section DerivedPasting

variable {A₀ : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory A₀]
variable {B₀ : Type*} [Category B₀] [Abelian B₀] [HasDerivedCategory B₀]
variable {C₀ : Type*} [Category C₀] [Abelian C₀] [HasDerivedCategory C₀]
variable {D₀ : Type*} [Category D₀] [Abelian D₀] [HasDerivedCategory D₀]
variable {E₀ : Type*} [Category E₀] [Abelian E₀] [HasDerivedCategory E₀]
variable {F₀ : Type*} [Category F₀] [Abelian F₀] [HasDerivedCategory F₀]
variable (J₀ : A₀ ⥤ B₀) (J₁ : C₀ ⥤ D₀) (J₂ : E₀ ⥤ F₀)
  (P₁ : D₀ ⥤ B₀) (P₂ : F₀ ⥤ D₀) (R₁ : C₀ ⥤ A₀) (R₂ : E₀ ⥤ C₀)
  (P : F₀ ⥤ B₀) (R : E₀ ⥤ A₀)
variable [J₀.Additive] [PreservesFiniteLimits J₀] [PreservesFiniteColimits J₀]
variable [J₁.Additive] [PreservesFiniteLimits J₁] [PreservesFiniteColimits J₁]
variable [J₂.Additive] [PreservesFiniteLimits J₂] [PreservesFiniteColimits J₂]
variable [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
variable [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
variable [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
variable [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
variable [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem derivedSquare_vertical
    (ep : P ≅ P₂ ⋙ P₁) (er : R ≅ R₂ ⋙ R₁)
    (t₁ : J₁ ⋙ P₁ ⟶ R₁ ⋙ J₀) (t₂ : J₂ ⋙ P₂ ⟶ R₂ ⋙ J₁)
    (t : J₂ ⋙ P ⟶ R ⋙ J₀)
    (ht : ∀ X, ep.hom.app (J₂.obj X) ≫ P₁.map (t₂.app X) ≫ t₁.app (R₂.obj X) =
      t.app X ≫ J₀.map (er.hom.app X)) (N : DerivedCategory E₀) :
    (Functor.mapDerivedCategoryNatIso ep ≪≫
        Functor.mapDerivedCategoryCompIso P₂ P₁).hom.app (J₂.mapDerivedCategory.obj N) ≫
        P₁.mapDerivedCategory.map ((derivedSquare J₂ P₂ R₂ J₁ t₂).app N) ≫
        (derivedSquare J₁ P₁ R₁ J₀ t₁).app (R₂.mapDerivedCategory.obj N) =
      (derivedSquare J₂ P R J₀ t).app N ≫ J₀.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso er ≪≫
          Functor.mapDerivedCategoryCompIso R₂ R₁).hom.app N) := by
  let ep' := Functor.mapDerivedCategoryNatIso ep ≪≫ Functor.mapDerivedCategoryCompIso P₂ P₁
  let er' := Functor.mapDerivedCategoryNatIso er ≪≫ Functor.mapDerivedCategoryCompIso R₂ R₁
  let a₁ := derivedSquare J₁ P₁ R₁ J₀ t₁
  let a₂ := derivedSquare J₂ P₂ R₂ J₁ t₂
  let a := derivedSquare J₂ P R J₀ t
  let L : J₂.mapDerivedCategory ⋙ P.mapDerivedCategory ⟶
      R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory ⋙ J₀.mapDerivedCategory :=
    Functor.whiskerLeft J₂.mapDerivedCategory ep'.hom ≫
      Functor.whiskerRight a₂ P₁.mapDerivedCategory ≫
      Functor.whiskerLeft R₂.mapDerivedCategory a₁
  let H : J₂.mapDerivedCategory ⋙ P.mapDerivedCategory ⟶
      R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory ⋙ J₀.mapDerivedCategory :=
    a ≫ Functor.whiskerRight er'.hom J₀.mapDerivedCategory
  suffices he : L = H from congr_app he N
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso E₀ (.up ℤ)) (fun K ↦ ?_)
  dsimp only [L, H, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  let K₂ := (R₂.mapHomologicalComplex (.up ℤ)).obj K
  let K₁ := (R₁.mapHomologicalComplex (.up ℤ)).obj K₂
  rw [← cancel_mono (J₀.mapDerivedCategory.map
    (R₁.mapDerivedCategory.map (R₂.mapDerivedCategoryFactors.hom.app K)) ≫
    J₀.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.hom.app K₂) ≫
    J₀.mapDerivedCategoryFactors.hom.app K₁)]
  simp only [Category.assoc]
  have n₁ := a₁.naturality (R₂.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at n₁
  rw [← reassoc_of% n₁, derivedSquare_fac J₁ P₁ R₁ J₀ t₁ K₂]
  have h₂fac := congrArg P₁.mapDerivedCategory.map (derivedSquare_fac J₂ P₂ R₂ J₁ t₂ K)
  simp only [Functor.map_comp] at h₂fac
  rw [reassoc_of% h₂fac]
  have n₂ := P₁.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at n₂
  change P₁.mapDerivedCategory.map
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K)) ≫
      P₁.mapDerivedCategoryFactors.hom.app ((J₁.mapHomologicalComplex (.up ℤ)).obj K₂) =
    P₁.mapDerivedCategoryFactors.hom.app
      ((P₂.mapHomologicalComplex (.up ℤ)).obj ((J₂.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map ((P₁.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K)) at n₂
  rw [reassoc_of% n₂]
  have n₃ := ep'.hom.naturality (J₂.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at n₃
  rw [← reassoc_of% n₃, reassoc_of% (derivedTriangle_fac P₂ P₁ P ep _)]
  have hr' := congrArg J₀.mapDerivedCategory.map (derivedTriangle_fac R₂ R₁ R er K)
  simp only [Functor.map_comp] at hr'
  rw [reassoc_of% hr']
  have n₄ := J₀.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at n₄
  change J₀.mapDerivedCategory.map (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K)) ≫
      J₀.mapDerivedCategoryFactors.hom.app K₁ =
    J₀.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((J₀.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K)) at n₄
  rw [n₄, reassoc_of% (derivedSquare_fac J₂ P R J₀ t K)]
  simp only [← DerivedCategory.Q.map_comp]
  have hc : (NatTrans.mapHomologicalComplex ep.hom (.up ℤ)).app
        ((J₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (P₁.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app K₂ =
    (NatTrans.mapHomologicalComplex t (.up ℤ)).app K ≫
      (J₀.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex er.hom (.up ℤ)).app K) := by
    ext n
    change ep.hom.app (J₂.obj (K.X n)) ≫ P₁.map (t₂.app (K.X n)) ≫
      t₁.app (R₂.obj (K.X n)) = t.app (K.X n) ≫ J₀.map (er.hom.app (K.X n))
    exact ht (K.X n)
  exact congrArg (fun f ↦ P.mapDerivedCategory.map (J₂.mapDerivedCategoryFactors.hom.app K) ≫
    P.mapDerivedCategoryFactors.hom.app ((J₂.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map f) hc

end DerivedPasting

section DerivedHorizontal

variable {A₀ : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory A₀]
variable {B₀ : Type*} [Category B₀] [Abelian B₀] [HasDerivedCategory B₀]
variable {C₀ : Type*} [Category C₀] [Abelian C₀] [HasDerivedCategory C₀]
variable {D₀ : Type*} [Category D₀] [Abelian D₀] [HasDerivedCategory D₀]
variable {E₀ : Type*} [Category E₀] [Abelian E₀] [HasDerivedCategory E₀]
variable {F₀ : Type*} [Category F₀] [Abelian F₀] [HasDerivedCategory F₀]
variable (K : A₀ ⥤ B₀) (L : B₀ ⥤ E₀) (I : C₀ ⥤ D₀) (J : D₀ ⥤ F₀)
  (R : C₀ ⥤ A₀) (P : D₀ ⥤ B₀) (Q : F₀ ⥤ E₀) (I' : C₀ ⥤ F₀) (K' : A₀ ⥤ E₀)
variable [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
variable [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
variable [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
variable [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
variable [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
variable [I'.Additive] [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
variable [K'.Additive] [PreservesFiniteLimits K'] [PreservesFiniteColimits K']

private theorem derivedSquare_horizontal
    (ei : I ⋙ J ≅ I') (ek : K ⋙ L ≅ K')
    (t₁ : I ⋙ P ⟶ R ⋙ K) (t₂ : J ⋙ Q ⟶ P ⋙ L) (t : I' ⋙ Q ⟶ R ⋙ K')
    (ht : ∀ X, Q.map (ei.hom.app X) ≫ t.app X =
      t₂.app (I.obj X) ≫ L.map (t₁.app X) ≫ ek.hom.app (R.obj X))
    (N : DerivedCategory C₀) :
    Q.mapDerivedCategory.map (((Functor.mapDerivedCategoryCompIso I J).symm ≪≫
      Functor.mapDerivedCategoryNatIso ei).hom.app N) ≫
        (derivedSquare I' Q R K' t).app N =
      (derivedSquare J Q P L t₂).app (I.mapDerivedCategory.obj N) ≫
        L.mapDerivedCategory.map ((derivedSquare I P R K t₁).app N) ≫
        ((Functor.mapDerivedCategoryCompIso K L).symm ≪≫
          Functor.mapDerivedCategoryNatIso ek).hom.app (R.mapDerivedCategory.obj N) := by
  let ei' := (Functor.mapDerivedCategoryCompIso I J).symm ≪≫
    Functor.mapDerivedCategoryNatIso ei
  let ek' := (Functor.mapDerivedCategoryCompIso K L).symm ≪≫
    Functor.mapDerivedCategoryNatIso ek
  let a₁ := derivedSquare I P R K t₁
  let a₂ := derivedSquare J Q P L t₂
  let a := derivedSquare I' Q R K' t
  let lhs : I.mapDerivedCategory ⋙ J.mapDerivedCategory ⋙ Q.mapDerivedCategory ⟶
      R.mapDerivedCategory ⋙ K'.mapDerivedCategory :=
    Functor.whiskerRight ei'.hom Q.mapDerivedCategory ≫ a
  let rhs : I.mapDerivedCategory ⋙ J.mapDerivedCategory ⋙ Q.mapDerivedCategory ⟶
      R.mapDerivedCategory ⋙ K'.mapDerivedCategory :=
    Functor.whiskerLeft I.mapDerivedCategory a₂ ≫
      Functor.whiskerRight a₁ L.mapDerivedCategory ≫
      Functor.whiskerLeft R.mapDerivedCategory ek'.hom
  suffices he : lhs = rhs from congr_app he N
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₀ (.up ℤ)) (fun X ↦ ?_)
  dsimp only [lhs, rhs, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  let XR := (R.mapHomologicalComplex (.up ℤ)).obj X
  let XI := (I.mapHomologicalComplex (.up ℤ)).obj X
  rw [← cancel_mono (K'.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app X) ≫
    K'.mapDerivedCategoryFactors.hom.app XR)]
  simp only [Category.assoc]
  have nk := ek'.hom.naturality (R.mapDerivedCategoryFactors.hom.app X)
  dsimp only [Functor.comp_map] at nk
  rw [← reassoc_of% nk, derivedComp_fac K L K' ek XR]
  have h₁ := congrArg L.mapDerivedCategory.map (derivedSquare_fac I P R K t₁ X)
  simp only [Functor.map_comp] at h₁
  rw [reassoc_of% h₁]
  have n₁ := L.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X)
  dsimp only [Functor.comp_map] at n₁
  change L.mapDerivedCategory.map
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X)) ≫
      L.mapDerivedCategoryFactors.hom.app ((K.mapHomologicalComplex (.up ℤ)).obj XR) =
    L.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj XI) ≫
      DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X)) at n₁
  rw [reassoc_of% n₁]
  have n₂ := a₂.naturality (I.mapDerivedCategoryFactors.hom.app X)
  dsimp only [Functor.comp_map] at n₂
  rw [← reassoc_of% n₂, reassoc_of% (derivedSquare_fac J Q P L t₂ XI),
    derivedSquare_fac I' Q R K' t X]
  have hi := congrArg Q.mapDerivedCategory.map (derivedComp_fac I J I' ei X)
  simp only [Functor.map_comp] at hi
  rw [reassoc_of% hi]
  have n₃ := Q.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex ei.hom (.up ℤ)).app X)
  dsimp only [Functor.comp_map] at n₃
  erw [reassoc_of% n₃]
  simp only [← DerivedCategory.Q.map_comp]
  have hc : (Q.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex ei.hom (.up ℤ)).app X) ≫
      (NatTrans.mapHomologicalComplex t (.up ℤ)).app X =
    (NatTrans.mapHomologicalComplex t₂ (.up ℤ)).app XI ≫
      (L.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex t₁ (.up ℤ)).app X) ≫
      (NatTrans.mapHomologicalComplex ek.hom (.up ℤ)).app XR := by
    ext n
    change Q.map (ei.hom.app (X.X n)) ≫ t.app (X.X n) =
      t₂.app (I.obj (X.X n)) ≫ L.map (t₁.app (X.X n)) ≫ ek.hom.app (R.obj (X.X n))
    exact ht (X.X n)
  exact congrArg (fun f ↦ Q.mapDerivedCategory.map
    (J.mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app X)) ≫
    Q.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app XI) ≫
    Q.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (.up ℤ)).obj XI) ≫
    DerivedCategory.Q.map f) hc

end DerivedHorizontal


attribute [local irreducible] moduleAlpha moduleGComp moduleJComp

/-- The system clopen projection is identity on its image and zero on the complement.
Source: Stacks 09AE; node proof Step 4
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: split every test object into its pullbacks of the clopen image and its
complement. The sheaf axiom identifies its sections with the product of the two
section modules. The unit followed by inverse open-to-direct comparison is (x,y) ↦
(x,0). The horizontal restrictions are semilinear componentwise maps, so they
commute with this projection, as do module maps and differentials. -/
theorem modulePi_components {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Modules R φ X) :
    (pull R φ s).map ((modulePi R φ s).app M) =
        (moduleJAdj R φ s).unit.app ((pull R φ s).obj M) ∧
      (pull R φ c).map ((modulePi R φ s).app M) = 0 := by
  sorry

/-- Intrinsic moduleAlpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: after beta, the two clopen projections select nested open components.
On every test object's intersections of the two clopen decompositions the two
composites are both identity or both zero. Sheaf uniqueness proves equality,
each map already commutes with the semilinear transitions, so this is an equality of system maps. -/
theorem moduleAlpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Modules R φ E) :
    (moduleGComp R φ p₁ p₂).hom.app ((extension R φ j).obj N) ≫
        (pull R φ p₁).map ((moduleAlpha R φ i r₂ p₂ j h₂).app N) ≫
        (moduleAlpha R φ k r₁ p₁ i h₁).app ((pull R φ r₂).obj N) =
      (moduleAlpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (extension R φ k).map ((moduleGComp R φ r₁ r₂).hom.app N) := by
  sorry

/-- Intrinsic moduleAlpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the first clopen projection selects l(W), and the second selects lk(V)
inside it. Their composite selects lk(V) and vanishes on its complement. Use the
open-composition beta equation and exact localization to identify the displayed maps. -/
theorem moduleAlpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Modules R φ C) :
    (pull R φ q).map ((moduleJComp R φ i j).hom.app N) ≫
        (moduleAlpha R φ (k ≫ l) r q (i ≫ j) h).app N =
      (moduleAlpha R φ l p q j h₂).app ((extension R φ i).obj N) ≫
        (extension R φ l).map ((moduleAlpha R φ k r p i h₁).app N) ≫
        (moduleJComp R φ k l).hom.app ((pull R φ r).obj N) := by
  sorry

/-- Intrinsic alpha agrees with vertical pasting on every input.
Source: Stacks, Tag 0F7C and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: after beta, the two clopen projections select nested open components.
On every test object's intersections of the two clopen decompositions the two
composites are both identity or both zero. Sheaf uniqueness proves equality,
termwise extension preserves it, and exact localization descends it. -/
theorem alpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (N : Derived R φ E) :
    (gComp R φ p₁ p₂).hom.app ((J R φ j).obj N) ≫
        (G R φ p₁).map ((alpha R φ i r₂ p₂ j h₂).app N) ≫
        (alpha R φ k r₁ p₁ i h₁).app ((G R φ r₂).obj N) =
      (alpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
        (J R φ k).map ((gComp R φ r₁ r₂).hom.app N) := by
  simpa only [alpha, gComp, derivedSquare] using
    derivedSquare_vertical
      (extension R φ k) (extension R φ i) (extension R φ j)
      (pull R φ p₁) (pull R φ p₂) (pull R φ r₁) (pull R φ r₂)
      (pull R φ (p₁ ≫ p₂)) (pull R φ (r₁ ≫ r₂))
      (moduleGComp R φ p₁ p₂) (moduleGComp R φ r₁ r₂)
      (moduleAlpha R φ k r₁ p₁ i h₁) (moduleAlpha R φ i r₂ p₂ j h₂)
      (moduleAlpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
      (fun X ↦ moduleAlpha_vertical R φ k i j r₁ r₂ p₁ p₂ h₁ h₂ h X) N

/-- Intrinsic alpha agrees with horizontal pasting on every input.
Source: Stacks, Tag 0F7D and blueprint, fifth proof step
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the first clopen projection selects l(W), and the second selects lk(V)
inside it. Their composite selects lk(V) and vanishes on its complement. Use the
open-composition beta equation and exact localization to identify the displayed maps. -/
theorem alpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (N : Derived R φ C) :
    (G R φ q).map ((jComp R φ i j).hom.app N) ≫
        (alpha R φ (k ≫ l) r q (i ≫ j) h).app N =
      (alpha R φ l p q j h₂).app ((J R φ i).obj N) ≫
        (J R φ l).map ((alpha R φ k r p i h₁).app N) ≫
        (jComp R φ k l).hom.app ((G R φ r).obj N) := by
  simpa only [alpha, jComp, derivedSquare] using
    derivedSquare_horizontal
      (extension R φ k) (extension R φ l) (extension R φ i) (extension R φ j)
      (pull R φ r) (pull R φ p) (pull R φ q)
      (extension R φ (i ≫ j)) (extension R φ (k ≫ l))
      (moduleJComp R φ i j) (moduleJComp R φ k l)
      (moduleAlpha R φ k r p i h₁) (moduleAlpha R φ l p q j h₂)
      (moduleAlpha R φ (k ≫ l) r q (i ≫ j) h)
      (fun X ↦ moduleAlpha_horizontal R φ k l i j r p q h₁ h₂ h X) N

/-- Both normalized proper/open mate-pasting laws, as system transformations.
Source: Stacks 0F7C, 0F7D and the varying-ring extension of the local-pairs argument
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof (the node's eleven steps):
1. Apply the constant-ring geometric calculus, with ring Z, to obtain the clopen
   lift s=(k,r) into W ×_T S and its complementary open, without cartesianness.
2. Inverse image and direct-sum extension act on the same underlying abelian
   sheaves after restriction along φ. A semilinear transition sends [a,x] to
   [a,t(x)], with t(cx)=φ(c)t(x); exactness is componentwise.
3. Cartesian open comparison preserves the lift label under the fibre-product
   bijection. It is the inverse open-unit transpose moduleBeta. Both routes past
   a transition therefore send a generator to [a',t(x)]. Sheafify this equality.
4. On the two clopen components the projection is (x,y) ↦ (x,0). It commutes with
   every semilinear transition, restriction and differential. This is modulePi;
   composition with moduleBeta and the compositors gives moduleAlpha.
5. Inverse-image composition identifies iterated pullbacks, and open composition
   combines lift labels without changing sections. The section-normalized
   direct-image compositor and its conjugate fix these comparisons and units.
6. Vertically, the projections retain nested components. On the final retained
   component both composites are identity, and on every other component one
   projection is zero. Sheaf uniqueness proves moduleAlpha_vertical.
7. Horizontally the projections select l(W) and then lk(V) inside it. The same
   identity/zero calculation and the open compositor give moduleAlpha_horizontal.
8. Apply the simultaneous ordinary-derived section model. Localize these actual
   degreewise maps of systems, obtaining alpha and its two pasting equations.
   Equalities are not inferred from evaluation of arbitrary derived morphisms.
9. Take the proper-adjunction mate. Its definition is precisely eta_p, alpha
   whiskered by Rr, and Rp(k! epsilon_r), with the specified order.
10. mateEquiv_hcomp applied to Step 6 proves the first displayed law, and
    mateEquiv_vcomp applied to Step 7 proves the second. Conjugate comparisons
    transport from composite adjunctions to the intrinsic proper compositors.
11. Identity lift labels and projections give the identity mate via the triangle
    laws. Evaluation preserves the constructed maps, units and counits, so the
    evaluated mate is the arbitrary constant-R_n clopen-projection mate. This
    uses neither finite-coefficient invertibility nor faithfulness of evaluation. -/
theorem properOpenPasting :
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived R φ A),
      (J R φ j).map ((pComp R φ r₁ r₂).hom.app M) ≫
          (gamma R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (pComp R φ p₁ p₂).inv.app ((J R φ k).obj M) =
        (gamma R φ i r₂ p₂ j h₂).app ((P R φ r₁).obj M) ≫
          (P R φ p₂).map ((gamma R φ k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived R φ A),
      (jComp R φ i j).hom.app ((P R φ r).obj M) ≫
          (gamma R φ (k ≫ l) r q (i ≫ j) h).app M ≫
          (P R φ q).map ((jComp R φ k l).inv.app M) =
        (J R φ j).map ((gamma R φ k r p i h₁).app M) ≫
          (gamma R φ l p q j h₂).app ((J R φ k).obj M)) := by
  constructor
  · intro A C E B₀ D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    let a₁ := TwoSquare.mk _ _ _ _ (alpha R φ k r₁ p₁ i h₁)
    let a₂ := TwoSquare.mk _ _ _ _ (alpha R φ i r₂ p₂ j h₂)
    let a := TwoSquare.mk _ _ _ _ (alpha R φ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    have ha : TwoSquare.vComp a₂ a₁ =
        (a.whiskerLeft (gComp R φ r₁ r₂).hom).whiskerRight
          (gComp R φ p₁ p₂).inv := by
      apply TwoSquare.ext
      intro N
      dsimp [a₁, a₂, a, TwoSquare.vComp, TwoSquare.whiskerLeft,
        TwoSquare.whiskerRight]
      simpa [TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using
        (congrArg (fun f ↦ (gComp R φ p₁ p₂).inv.app ((J R φ j).obj N) ≫ f)
          (alpha_vertical R φ k i j r₁ r₂ p₁ p₂ h₁ h₂ h N))
    have hm := congrArg
      (mateEquiv ((adj R φ r₂).comp (adj R φ r₁))
        ((adj R φ p₂).comp (adj R φ p₁))) ha
    rw [mateEquiv_hcomp,
      mateEquiv_conjugateEquiv_vcomp _ (adj R φ (p₁ ≫ p₂)),
      conjugateEquiv_mateEquiv_vcomp _ (adj R φ (r₁ ≫ r₂))] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    simpa only [a₁, a₂, a, gamma, pComp, conjugateIsoEquiv_apply_hom,
      conjugateIsoEquiv_apply_inv, TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hmM.symm
  · intro A C E B₀ D F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    let a₁ := TwoSquare.mk _ _ _ _ (alpha R φ k r p i h₁)
    let a₂ := TwoSquare.mk _ _ _ _ (alpha R φ l p q j h₂)
    let a := TwoSquare.mk _ _ _ _ (alpha R φ (k ≫ l) r q (i ≫ j) h)
    have ha : TwoSquare.hComp a₁ a₂ =
        (a.whiskerTop (jComp R φ i j).hom).whiskerBottom
          (jComp R φ k l).inv := by
      apply TwoSquare.ext
      intro N
      dsimp [a₁, a₂, a, TwoSquare.hComp, TwoSquare.whiskerTop,
        TwoSquare.whiskerBottom]
      have hh := alpha_horizontal R φ k l i j r p q h₁ h₂ h N
      have hh' := congrArg
        (fun f ↦ f ≫ (jComp R φ k l).inv.app ((G R φ r).obj N)) hh
      simpa [TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using hh'.symm
    have hm := congrArg (mateEquiv (adj R φ r) (adj R φ q)) ha
    rw [mateEquiv_vcomp (adj R φ r) (adj R φ p) (adj R φ q)] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    rw [show (a.whiskerTop (jComp R φ i j).hom).whiskerBottom
        (jComp R φ k l).inv =
        Functor.whiskerRight (jComp R φ i j).hom (G R φ q) ≫ a ≫
          Functor.whiskerLeft (G R φ r) (jComp R φ k l).inv from by
          simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, Category.assoc],
      mate_whisker] at hmM
    simpa only [a₁, a₂, a, gamma, TwoSquare.vComp, TwoSquare.mk,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hmM.symm

/-- Identity normalizations of the intrinsic inverse-image/open-extension arrow.
Source: Stacks 07A7, 0F7B; node proof Steps 5 and 11
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the identity square has the identity lift and its projection retains the
entire component. The unit normalization of beta and the identity compositors
therefore gives these equalities already on system complexes; localize them. -/
theorem alpha_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (alpha R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (J R φ j).map ((gId R φ U).hom.app M) =
        (gId R φ X).hom.app ((J R φ j).obj M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ X),
      (alpha R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (jId R φ U).hom.app ((G R φ p).obj M) =
        (G R φ p).map ((jId R φ X).hom.app M)) := by
  sorry

/-- Identity normalizations of gamma in both directions.
Source: Stacks, Tags 0F7B and 07A7, blueprint, steps 6 and 10
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: the clopen projection is identity for either identity square. Its alpha is the
canonical inverse-image/open-extension identity; taking the mate and using the
triangle identities gives the corresponding identity on direct image or extension. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived R φ U),
      (gamma R φ j (𝟙 U) (𝟙 X) j h).app M ≫
          (pId R φ X).hom.app ((J R φ j).obj M) =
        (J R φ j).map ((pId R φ U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived R φ U),
      (gamma R φ (𝟙 U) p p (𝟙 X) h).app M ≫
          (P R φ p).map ((jId R φ U).hom.app M) =
        (jId R φ X).hom.app ((P R φ p).obj M)) := by
  constructor
  · intro U X j _ _ h M
    let a := TwoSquare.mk _ _ _ _ (alpha R φ j (𝟙 U) (𝟙 X) j h)
    have ha : (a.whiskerLeft (gId R φ U).hom).whiskerRight
        (gId R φ X).inv = TwoSquare.vId (J R φ j) := by
      apply TwoSquare.ext
      intro N
      dsimp [a, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vId]
      simpa [TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using
        (congrArg (fun f ↦ (gId R φ X).inv.app ((J R φ j).obj N) ≫ f)
          ((alpha_identities R φ).1 j h N))
    have hm := congrArg (mateEquiv Adjunction.id Adjunction.id) ha
    rw [mateEquiv_conjugateEquiv_vcomp _ (adj R φ (𝟙 X)),
      conjugateEquiv_mateEquiv_vcomp _ (adj R φ (𝟙 U))] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    have hh : (J R φ j).map ((pId R φ U).inv.app M) ≫
        (gamma R φ j (𝟙 U) (𝟙 X) j h).app M ≫
        (pId R φ X).hom.app ((J R φ j).obj M) = 𝟙 _ := by
      simpa [a, gamma, pId, conjugateIsoEquiv, TwoSquare.whiskerTop,
        TwoSquare.whiskerBottom, TwoSquare.vId, mateEquiv, Adjunction.id] using hmM
    have hh' := congrArg (fun f ↦ (J R φ j).map ((pId R φ U).hom.app M) ≫ f) hh
    simpa [← Category.assoc, ← Functor.map_comp] using hh'
  · intro U X p _ h M
    let a := TwoSquare.mk _ _ _ _ (alpha R φ (𝟙 U) p p (𝟙 X) h)
    have ha : (a.whiskerTop (jId R φ X).inv).whiskerBottom
        (jId R φ U).hom = TwoSquare.hId (G R φ p) := by
      apply TwoSquare.ext
      intro N
      dsimp [a, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hId]
      have hh := (alpha_identities R φ).2 p h N
      have hh' := congrArg
        (fun f ↦ (G R φ p).map ((jId R φ X).inv.app N) ≫ f) hh
      simpa [TwoSquare.mk, TwoSquare.natTrans, ← Functor.map_comp,
        Category.assoc] using hh'
    have hm := congrArg (mateEquiv (adj R φ p) (adj R φ p)) ha
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.natTrans, TwoSquare.mk, Category.assoc] at hm
    rw [mate_whisker] at hm
    have hmM := congrArg (fun s ↦ s.app M) hm
    have hh : (jId R φ X).inv.app ((P R φ p).obj M) ≫
        (gamma R φ (𝟙 U) p p (𝟙 X) h).app M ≫
        (P R φ p).map ((jId R φ U).hom.app M) = 𝟙 _ := by
      simpa [a, gamma, TwoSquare.hId, mateEquiv] using hmM
    have hh' := congrArg
      (fun f ↦ (jId R φ X).hom.app ((P R φ p).obj M) ≫ f) hh
    simpa only [← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp, Category.comp_id] using hh'


/-- Evaluation gives exactly the arbitrary constant-R_n clopen-projection mate.
Source: node proof Step 11, Stacks 0F7B
(blueprint: lem-sp-varying-ring-proper-open-pasting).
Proof: ordinary evaluations preserve the lift comparison and the clopen
identity/zero projection. Thus they carry moduleAlpha to the constant-ring alpha.
Localization preserves these actual comparisons. The normalized mate-evaluation
identity from lem-coef-semilinear-derived-sections, using both unit and counit
equations, identifies gamma with the evaluated constant-ring mate. Constant
embedding followed by evaluation is identity, which is exactly constantGamma.
This works for arbitrary, including infinite, R_n. -/
theorem gamma_evaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived R φ V) (n : ℕ) :
    (ev R φ T n).map ((gamma R φ k r p i h).app M) ≫
        (evalP R φ p n).hom.app ((J R φ k).obj M) ≫
        (StrictTower.moduleDirectImage (R n) p).rightDerivedFunctor.map
          ((evalJ R φ k n).hom.app M) =
      (evalJ R φ i n).hom.app ((P R φ r).obj M) ≫
        (StrictTower.moduleJ (R n) i).mapDerivedCategory.map
          ((evalP R φ r n).hom.app M) ≫
        constantGamma (R n) k r p i h ((ev R φ V n).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
