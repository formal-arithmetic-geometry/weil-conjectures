/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenData
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientSystemBetaLocalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting

/-! # Ambient SystemClopenLocalization

Source: Stacks Project, Tags 015F, 07A7 and 0F7B.
(blueprint: lem-sf-ambient-system-clopen-localization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ w₁ w₂ h₁ h₂
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientClopen

private theorem adjunction_on_complexes
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    AdjunctionOnComplexes a a.mapExactDerivedCategory := by
  constructor
  · intro K
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      G.mapDerivedCategoryFactors.inv.app _ ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app _ = _
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  · intro K
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
    rfl

private theorem localize_fac
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] {F G : A ⥤ B}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⟶ G) (K : CochainComplex A ℤ) :
    (localize a).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  simp only [localize, Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem adjunction_on_complexes_unit
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    {L : A ⥤ D} {R : D ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (K : CochainComplex A ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) :=
  (adjunction_on_complexes a).1 K

private theorem projector_restriction_descent
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ⊣ F) (p : 𝟭 A ⟶ F ⋙ H)
    (d : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (hd : ∀ K : CochainComplex A ℤ,
      d.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K)) :
    ∀ M, F.mapDerivedCategory.map (d.app M) =
      (a.mapExactDerivedCategory).unit.app (F.mapDerivedCategory.obj M) := by
  have he : Functor.whiskerRight d F.mapDerivedCategory =
      Functor.whiskerLeft F.mapDerivedCategory (a.mapExactDerivedCategory).unit := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    change F.mapDerivedCategory.map (d.app (DerivedCategory.Q.obj K)) =
      (a.mapExactDerivedCategory).unit.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K))
    apply (cancel_mono
      (F.mapDerivedCategory.map
        (H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj K)))).1
    erw [← F.mapDerivedCategory.map_comp_assoc, hd,
      Functor.mapDerivedCategoryFactors_hom_naturality]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (a.mapExactDerivedCategory).unit.naturality (F.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    erw [← reassoc_of% hn, adjunction_on_complexes_unit]
    congr 2
    apply HomologicalComplex.hom_ext
    intro n
    exact hp (K.X n)
  intro M
  exact NatTrans.congr_app he M

private theorem localized_projector
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ⊣ F) (R : DerivedCategory D ⥤ DerivedCategory A)
    (b : F.mapDerivedCategory ⊣ R) (t : H.mapDerivedCategory ⟶ R) [IsIso t]
    (p : 𝟭 A ⟶ F ⋙ H)
    (e : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (he : ∀ M, F.mapDerivedCategory.map (e.app M) =
      a.mapExactDerivedCategory.unit.app (F.mapDerivedCategory.obj M)) :
    (Functor.mapDerivedCategoryIdIso A).inv ≫ localize p ≫
      (Functor.mapDerivedCategoryCompIso F H).hom = e := by
  apply StrictTower.projector_unique b t
  have hd := projector_restriction_descent F H a p
    ((Functor.mapDerivedCategoryIdIso A).inv ≫ localize p ≫
      (Functor.mapDerivedCategoryCompIso F H).hom) hp (fun K ↦ ?_)
  · intro M
    exact (hd M).trans (he M).symm
  · simp only [NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, localize_fac]
    rw [← Functor.mapDerivedCategoryIdIso_hom_app_Q_obj]
    simp only [Iso.inv_hom_id_app_assoc]

private theorem localized_projector_heq
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (F F' : A ⥤ D) (H H' : D ⥤ A)
    [F.Additive] [F'.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (a : H ⊣ F) (a' : H' ⊣ F') (R : DerivedCategory D ⥤ DerivedCategory A)
    (b : F'.mapDerivedCategory ⊣ R) (t : H'.mapDerivedCategory ⟶ R) [IsIso t]
    (p : 𝟭 A ⟶ F ⋙ H)
    (e : 𝟭 (DerivedCategory A) ⟶ F'.mapDerivedCategory ⋙ H'.mapDerivedCategory)
    (hF : F = F') (hH : H = H') (ha : HEq a a')
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (he : ∀ M, F'.mapDerivedCategory.map (e.app M) =
      a'.mapExactDerivedCategory.unit.app (F'.mapDerivedCategory.obj M)) :
    HEq ((Functor.mapDerivedCategoryIdIso A).inv ≫ localize p ≫
      (Functor.mapDerivedCategoryCompIso F H).hom) e := by
  subst F'
  subst H'
  cases ha
  exact (localized_projector F H a R b t p e hp he).heq

attribute [local instance] VaryingRing.pullAdditive VaryingRing.pullLimits
  VaryingRing.pullColimits VaryingRing.extensionAdditive VaryingRing.extensionLimits
  VaryingRing.extensionColimits

private theorem system_projector_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U X D : Scheme.{u}} (s : U ⟶ X) (c : D ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) :
    HEq ((Functor.mapDerivedCategoryIdIso (VaryingRing.Modules C τ X)).inv ≫
      localize (VaryingRing.modulePi C τ s) ≫
      (Functor.mapDerivedCategoryCompIso (VaryingRing.pull C τ s)
        (VaryingRing.extension C τ s)).hom) (SemilinearProperOpen.pi C τ s) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ s
  have := SemilinearProperOpen.pull_additive C τ s
  have := SemilinearProperOpen.pull_limits C τ s
  have := SemilinearProperOpen.pull_colimits C τ s
  have := SemilinearProperOpen.extension_additive C τ s
  have := SemilinearProperOpen.extension_limits C τ s
  have := SemilinearProperOpen.extension_colimits C τ s
  have := SemilinearProperOpen.openToS_isIso C τ s
  exact localized_projector_heq
    (VaryingRing.pull C τ s) (SemilinearProperOpen.pull C τ s)
    (VaryingRing.extension C τ s) (SemilinearProperOpen.extension C τ s)
    (VaryingRing.moduleJAdj C τ s) (SemilinearProperOpen.ordinaryOpenAdj C τ s)
    (SemilinearProperOpen.R C τ s) (SemilinearProperOpen.adj C τ s)
    (SemilinearProperOpen.openToS C τ s) (VaryingRing.modulePi C τ s)
    (SemilinearProperOpen.pi C τ s) (SemilinearProperOpen.pull_eq C τ s).symm
    (SemilinearProperOpen.extension_eq C τ s).symm
    (chosen_adj_congr _ _ (SemilinearProperOpen.pull_eq C τ s).symm)
    (fun M ↦ (VaryingRing.modulePi_components C τ s c hc M).1)
    (fun M ↦ (SemilinearProperOpen.pi_components C τ s c hc M).1)

private theorem symm_iso_heq
    {A B : Type*} [Category A] [Category B] {F F' G G' : A ⥤ B}
    (e : F ≅ G) (e' : F' ≅ G') (hF : F = F') (hG : G = G') (he : HEq e e') :
    HEq e.symm e'.symm := by
  subst F'
  subst G'
  cases he
  rfl

private theorem localized_comp_iso_heq
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (F F' : A ⥤ B) (G G' : B ⥤ D) (H H' : A ⥤ D)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (e : F ⋙ G ≅ H) (e' : F' ⋙ G' ≅ H')
    (hF : F = F') (hG : G = G') (hH : H = H') (he : HEq e e') :
    HEq ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso e)
      ((Functor.mapDerivedCategoryCompIso F' G').symm ≪≫
        Functor.mapDerivedCategoryNatIso e') := by
  subst F'
  subst G'
  subst H'
  cases he
  rfl

attribute [local instance] SemilinearProperOpen.openPull_isRightAdjoint
  SemilinearProperOpen.pull_additive SemilinearProperOpen.pull_limits
  SemilinearProperOpen.pull_colimits SemilinearProperOpen.extension_additive
  SemilinearProperOpen.extension_limits SemilinearProperOpen.extension_colimits

private theorem ordinary_open_comp_heq
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    HEq (VaryingRing.moduleJComp C τ j b)
      ((WeilConjectures.AmbientCompositor.systems C τ).ordinaryE j b) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ j
  have := SemilinearProperOpen.pull_additive C τ j
  have := SemilinearProperOpen.pull_limits C τ j
  have := SemilinearProperOpen.pull_colimits C τ j
  have := SemilinearProperOpen.extension_additive C τ j
  have := SemilinearProperOpen.extension_limits C τ j
  have := SemilinearProperOpen.extension_colimits C τ j
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ b
  have := SemilinearProperOpen.pull_additive C τ b
  have := SemilinearProperOpen.pull_limits C τ b
  have := SemilinearProperOpen.pull_colimits C τ b
  have := SemilinearProperOpen.extension_additive C τ b
  have := SemilinearProperOpen.extension_limits C τ b
  have := SemilinearProperOpen.extension_colimits C τ b
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ (j ≫ b)
  have := SemilinearProperOpen.pull_additive C τ (j ≫ b)
  have := SemilinearProperOpen.pull_limits C τ (j ≫ b)
  have := SemilinearProperOpen.pull_colimits C τ (j ≫ b)
  have := SemilinearProperOpen.extension_additive C τ (j ≫ b)
  have := SemilinearProperOpen.extension_limits C τ (j ≫ b)
  have := SemilinearProperOpen.extension_colimits C τ (j ≫ b)
  have hj : HEq (VaryingRing.moduleJAdj C τ j)
      (SemilinearProperOpen.ordinaryOpenAdj C τ j) :=
    chosen_adj_congr _ _ (SemilinearProperOpen.pull_eq C τ j).symm
  have hb : HEq (VaryingRing.moduleJAdj C τ b)
      (SemilinearProperOpen.ordinaryOpenAdj C τ b) :=
    chosen_adj_congr _ _ (SemilinearProperOpen.pull_eq C τ b).symm
  have hjb : HEq (VaryingRing.moduleJAdj C τ (j ≫ b))
      (SemilinearProperOpen.ordinaryOpenAdj C τ (j ≫ b)) :=
    chosen_adj_congr _ _ (SemilinearProperOpen.pull_eq C τ (j ≫ b)).symm
  exact left_comp_heq
    (VaryingRing.moduleJAdj C τ j) (SemilinearProperOpen.ordinaryOpenAdj C τ j)
    (VaryingRing.moduleJAdj C τ b) (SemilinearProperOpen.ordinaryOpenAdj C τ b)
    (VaryingRing.moduleJAdj C τ (j ≫ b))
      (SemilinearProperOpen.ordinaryOpenAdj C τ (j ≫ b))
    (VaryingRing.moduleGComp C τ j b).symm (SemilinearProperOpen.pullComp C τ j b).symm
    (SemilinearProperOpen.extension_eq C τ j).symm
    (SemilinearProperOpen.pull_eq C τ j).symm
    (SemilinearProperOpen.extension_eq C τ b).symm
    (SemilinearProperOpen.pull_eq C τ b).symm
    (SemilinearProperOpen.extension_eq C τ (j ≫ b)).symm
    (SemilinearProperOpen.pull_eq C τ (j ≫ b)).symm hj hb hjb
    (symm_iso_heq _ _ (SemilinearProperOpen.pull_eq C τ (j ≫ b)).symm
      (congrArg₂ Functor.comp (SemilinearProperOpen.pull_eq C τ b).symm
        (SemilinearProperOpen.pull_eq C τ j).symm)
      (system_pull_comp_heq C τ j b).symm)

private theorem system_open_comp_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    HEq ((Functor.mapDerivedCategoryCompIso (VaryingRing.extension C τ j)
      (VaryingRing.extension C τ b)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (VaryingRing.moduleJComp C τ j b))
      (SemilinearProperOpen.jComp C τ j b) := by
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ j
  have := SemilinearProperOpen.pull_additive C τ j
  have := SemilinearProperOpen.pull_limits C τ j
  have := SemilinearProperOpen.pull_colimits C τ j
  have := SemilinearProperOpen.extension_additive C τ j
  have := SemilinearProperOpen.extension_limits C τ j
  have := SemilinearProperOpen.extension_colimits C τ j
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ b
  have := SemilinearProperOpen.pull_additive C τ b
  have := SemilinearProperOpen.pull_limits C τ b
  have := SemilinearProperOpen.pull_colimits C τ b
  have := SemilinearProperOpen.extension_additive C τ b
  have := SemilinearProperOpen.extension_limits C τ b
  have := SemilinearProperOpen.extension_colimits C τ b
  have := SemilinearProperOpen.openPull_isRightAdjoint C τ (j ≫ b)
  have := SemilinearProperOpen.pull_additive C τ (j ≫ b)
  have := SemilinearProperOpen.pull_limits C τ (j ≫ b)
  have := SemilinearProperOpen.pull_colimits C τ (j ≫ b)
  have := SemilinearProperOpen.extension_additive C τ (j ≫ b)
  have := SemilinearProperOpen.extension_limits C τ (j ≫ b)
  have := SemilinearProperOpen.extension_colimits C τ (j ≫ b)
  let o := WeilConjectures.AmbientCompositor.systems C τ
  have ho : o.e j b = SemilinearProperOpen.jComp C τ j b := by
    change Adjunction.leftAdjointCompIso _ _ _
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SemilinearProperOpen.pullComp C τ j b).symm) =
      Adjunction.leftAdjointCompIso _ _ _
        (Functor.mapDerivedCategoryNatIso (SemilinearProperOpen.pullComp C τ j b) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).symm
    congr 1
  have he := localized_comp_iso_heq
    (VaryingRing.extension C τ j) (SemilinearProperOpen.extension C τ j)
    (VaryingRing.extension C τ b) (SemilinearProperOpen.extension C τ b)
    (VaryingRing.extension C τ (j ≫ b)) (SemilinearProperOpen.extension C τ (j ≫ b))
    (VaryingRing.moduleJComp C τ j b) (o.ordinaryE j b)
    (SemilinearProperOpen.extension_eq C τ j).symm
    (SemilinearProperOpen.extension_eq C τ b).symm
    (SemilinearProperOpen.extension_eq C τ (j ≫ b)).symm (ordinary_open_comp_heq C τ j b)
  exact he.trans (((WeilConjectures.AmbientCompositor.open_localized o j b).symm.trans ho).heq)

private theorem hom_iso_heq
    {A : Type*} [Category A] {X X' Y Y' : A}
    (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y') (he : HEq e e') :
    HEq e.hom e'.hom := by
  subst X'
  subst Y'
  cases he
  rfl

private theorem system_open_cell_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion k] (h : j ≫ b = k) :
    HEq ((Functor.mapDerivedCategoryCompIso (VaryingRing.extension C τ j)
      (VaryingRing.extension C τ b)).inv ≫ localize
        ((VaryingRing.moduleJComp C τ j b).hom ≫ (VaryingRing.moduleJCongr C τ h).hom))
      ((SemilinearProperOpen.jComp C τ j b).hom ≫
        (SemilinearProperOpen.jCongr C τ h).hom) := by
  subst k
  have := SemilinearProperOpen.extension_additive C τ j
  have := SemilinearProperOpen.extension_limits C τ j
  have := SemilinearProperOpen.extension_colimits C τ j
  have := SemilinearProperOpen.extension_additive C τ b
  have := SemilinearProperOpen.extension_limits C τ b
  have := SemilinearProperOpen.extension_colimits C τ b
  have := SemilinearProperOpen.extension_additive C τ (j ≫ b)
  have := SemilinearProperOpen.extension_limits C τ (j ≫ b)
  have := SemilinearProperOpen.extension_colimits C τ (j ≫ b)
  simpa only [VaryingRing.moduleJCongr, SemilinearProperOpen.jCongr,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso, Localization.liftNatIso,
    Functor.isoWhiskerRight_hom, NatIso.mapHomologicalComplex, localize] using
    hom_iso_heq _ _ (congrArg₂ Functor.comp (SemilinearProperOpen.J_eq C τ j).symm
      (SemilinearProperOpen.J_eq C τ b).symm)
      (SemilinearProperOpen.J_eq C τ (j ≫ b)).symm (system_open_comp_localized C τ j b)

private theorem system_pull_cell_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    (h : j ≫ b = k) :
    HEq ((Functor.mapDerivedCategoryCompIso (VaryingRing.pull C τ b)
      (VaryingRing.pull C τ j)).inv ≫ localize
        ((VaryingRing.moduleGComp C τ j b).inv ≫
          (eqToIso (congrArg (VaryingRing.pull C τ) h)).hom))
      ((SemilinearProperOpen.pComp C τ j b).inv ≫
        (eqToIso (congrArg (SemilinearProperOpen.P C τ) h)).hom) := by
  subst k
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  change HEq ((Functor.mapDerivedCategoryCompIso _ _).inv ≫
    (Functor.mapDerivedCategoryNatIso (VaryingRing.moduleGComp C τ j b).symm).hom) _
  rw [Functor.mapDerivedCategoryNatIso_symm]
  exact iso_inv_heq _ _
    (SemilinearProperOpen.P_eq C τ (j ≫ b)).symm
    (congrArg₂ Functor.comp (SemilinearProperOpen.P_eq C τ b).symm
      (SemilinearProperOpen.P_eq C τ j).symm) (pcomp_heq C τ j b).symm

private theorem expanded_clopen_composite
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I : A ⥤ E) (P : E ⥤ D) (Q : A ⥤ B) (S : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R : A ⥤ C)
    (β : I ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R) :
    β ≫ Functor.whiskerRight (Functor.whiskerLeft Q π) B₀ ≫
      Functor.whiskerRight (Functor.associator Q S J).inv B₀ ≫
      (Functor.associator (Q ⋙ S) J B₀).hom ≫ Functor.whiskerLeft (Q ⋙ S) c ≫
      Functor.whiskerRight d K = clopenMateComposite I P Q S J B₀ K R β π c d := by
  apply NatTrans.ext
  funext M
  simp only [clopenMateComposite_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp]
  erw [B₀.map_id]
  simp only [Category.id_comp]

private theorem clopen_composite_localized
    (C : Fin 5 → Type v₁) [∀ i, Category.{h₁} (C i)]
    [∀ i, Abelian (C i)] [∀ i, HasDerivedCategory.{w₁} (C i)]
    (I : C 0 ⥤ₑ C 4) (P : C 4 ⥤ₑ C 3) (Q : C 0 ⥤ₑ C 1)
    (S : C 1 ⥤ₑ C 2) (J : C 2 ⥤ₑ C 1) (B : C 1 ⥤ₑ C 3)
    (K : C 2 ⥤ₑ C 3) (R : C 0 ⥤ₑ C 2)
    [I.obj.Additive] [P.obj.Additive] [Q.obj.Additive] [S.obj.Additive]
    [J.obj.Additive] [B.obj.Additive] [K.obj.Additive] [R.obj.Additive]
    (β : I.obj ⋙ P.obj ⟶ Q.obj ⋙ B.obj) (π : 𝟭 (C 1) ⟶ S.obj ⋙ J.obj)
    (c : J.obj ⋙ B.obj ⟶ K.obj) (d : Q.obj ⋙ S.obj ⟶ R.obj) :
    localizeSquare I.obj P.obj R.obj K.obj
      (clopenMateComposite I.obj P.obj Q.obj S.obj J.obj B.obj K.obj R.obj β π c d) =
    clopenMateComposite I.obj.mapDerivedCategory P.obj.mapDerivedCategory
      Q.obj.mapDerivedCategory S.obj.mapDerivedCategory J.obj.mapDerivedCategory
      B.obj.mapDerivedCategory K.obj.mapDerivedCategory R.obj.mapDerivedCategory
      (localizeSquare I.obj P.obj Q.obj B.obj β)
      ((Functor.mapDerivedCategoryIdIso (C 1)).inv ≫ localize π ≫
        (Functor.mapDerivedCategoryCompIso S.obj J.obj).hom)
      ((Functor.mapDerivedCategoryCompIso J.obj B.obj).inv ≫ localize c)
      ((Functor.mapDerivedCategoryCompIso Q.obj S.obj).inv ≫ localize d) := by
  let wi := ExactDerivedPasting.Word.edge I
  let wp := ExactDerivedPasting.Word.edge P
  let wq := ExactDerivedPasting.Word.edge Q
  let ws := ExactDerivedPasting.Word.edge S
  let wj := ExactDerivedPasting.Word.edge J
  let wb := ExactDerivedPasting.Word.edge B
  let wk := ExactDerivedPasting.Word.edge K
  let wr := ExactDerivedPasting.Word.edge R
  let e : ExactDerivedPasting.Expression C (.comp wi wp) (.comp wr wk) :=
    .vcomp (.cell (P := .comp wi wp) (R := .comp wq wb) β) (.vcomp (.output (.rightUnitInv wq) wb)
      (.vcomp (.output (.input wq (.cell (P := .nil 1) (R := .comp ws wj) π)) wb)
      (.vcomp (.output (.assocInv wq ws wj) wb)
        (.vcomp (.assoc (.comp wq ws) wj wb)
          (.vcomp (.input (.comp wq ws) (.cell (P := .comp wj wb) (R := wk) c))
            (.output (.cell (P := .comp wq ws) (R := wr) d) wk))))))
  have he := (ExactDerivedPasting.exact_derived_transformation_pasting C).1 e
  have ho : e.ordinary =
      clopenMateComposite I.obj P.obj Q.obj S.obj J.obj B.obj K.obj R.obj β π c d :=
    by
      dsimp only [e, ExactDerivedPasting.Expression.ordinary,
        ExactDerivedPasting.Word.ordinary, wi, wp, wq, ws, wj, wb, wk, wr]
      apply NatTrans.ext
      funext M
      simp only [clopenMateComposite_app, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Functor.associator_hom_app,
        Functor.rightUnitor_inv_app, Functor.comp_obj, Category.id_comp]
      erw [B.obj.map_id, B.obj.map_id]
      simp only [Category.id_comp]
  rw [ho] at he
  apply NatTrans.ext
  funext M
  have heM := congrArg (fun t ↦ t.app M) he.symm
  simp only [e, wi, wp, wq, ws, wj, wb, wk, wr,
    ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
    ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
    ExactDerivedPasting.Word.derived, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Iso.refl_inv,

    Category.comp_id, Category.id_comp, ExactFunctor.of_fst,
    Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
    localizeSquare, localize, clopenMateComposite_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.comp_obj,
    Category.assoc] at heM ⊢
  erw [B.obj.mapDerivedCategory.map_id, Category.id_comp,
    B.obj.mapDerivedCategory.map_id, Category.id_comp] at heM
  exact heM

private theorem clopen_composite_heq
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I I' : A ⥤ E) (P P' : E ⥤ D) (Q Q' : A ⥤ B) (S S' : B ⥤ C)
    (J J' : C ⥤ B) (B₀ B₀' : B ⥤ D) (K K' : C ⥤ D) (R R' : A ⥤ C)
    (β : I ⋙ P ⟶ Q ⋙ B₀) (π : 𝟭 B ⟶ S ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q ⋙ S ⟶ R)
    (β' : I' ⋙ P' ⟶ Q' ⋙ B₀') (π' : 𝟭 B ⟶ S' ⋙ J')
    (c' : J' ⋙ B₀' ⟶ K') (d' : Q' ⋙ S' ⟶ R')
    (hI : I = I') (hP : P = P') (hQ : Q = Q') (hS : S = S')
    (hJ : J = J') (hB : B₀ = B₀') (hK : K = K') (hR : R = R')
    (hβ : HEq β β') (hπ : HEq π π') (hc : HEq c c') (hd : HEq d d') :
    HEq (clopenMateComposite I P Q S J B₀ K R β π c d)
      (clopenMateComposite I' P' Q' S' J' B₀' K' R' β' π' c' d') := by
  subst I'
  subst P'
  subst Q'
  subst S'
  subst J'
  subst B₀'
  subst K'
  subst R'
  cases hβ
  cases hπ
  cases hc
  cases hd
  rfl

/-- Ambient SystemClopenLocalization. Source: Stacks Project, Tags 015F, 07A7 and 0F7B.
(blueprint: lem-sf-ambient-system-clopen-localization)

Proof: Identify the two ordinary direct images by their coefficient ring maps and use
adjoint uniqueness for their inverse images and open extensions. Their direct-image
compositors agree on every section, so their pullback compositors agree. Exact
localization preserves the inverse mate defining beta. The localized module projector
has composite with the canonical open-to-direct comparison equal to the proper unit;
this identifies it with the intrinsic projector. The normalized composite open
adjunction localizes to the composite exact open adjunction, fixing the open compositor.
Exact-derived transformation pasting now identifies the complete alpha words. Every
step occurs on the single sequence-site module category, before any evaluation. -/
theorem system_alpha_localized
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    HEq (localizeSquare _ _ _ _ (VaryingRing.moduleAlpha C τ k r p i h))
      (SemilinearProperOpen.alpha C τ k r p i h) := by
  let s := StrictTower.squareLift k r p i h
  have : IsOpenImmersion s := (StrictTower.squareLift_clopen k r p i h).1
  have : IsClosedImmersion s := (StrictTower.squareLift_clopen k r p i h).2
  let a := pullback.snd p i
  let b := pullback.fst p i
  let c : (pullback p i).Opens :=
    ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hc : Set.range c.ι = (Set.range s)ᶜ := Scheme.Opens.range_ι c
  let X : Fin 5 → Scheme.{u} := ![W, pullback p i, U, V, Z]
  let D (n : Fin 5) := VaryingRing.Modules C τ (X n)
  let : ∀ n, Category.{u + 1} (D n) := fun n ↦ inferInstance
  let : ∀ n, Abelian (D n) := fun n ↦ inferInstance
  let : ∀ n, HasDerivedCategory.{u + 2} (D n) := fun n ↦ inferInstance
  have : (ExactFunctor.of (VaryingRing.extension C τ i)).obj.Additive := by
    change (VaryingRing.extension C τ i).Additive
    infer_instance
  have : (ExactFunctor.of (VaryingRing.pull C τ p)).obj.Additive := by
    change (VaryingRing.pull C τ p).Additive
    infer_instance
  have : (ExactFunctor.of (VaryingRing.pull C τ a)).obj.Additive := by
    change (VaryingRing.pull C τ a).Additive
    infer_instance
  have : (ExactFunctor.of (VaryingRing.pull C τ s)).obj.Additive := by
    change (VaryingRing.pull C τ s).Additive
    infer_instance
  have : (ExactFunctor.of (VaryingRing.extension C τ s)).obj.Additive := by
    change (VaryingRing.extension C τ s).Additive
    infer_instance
  have : (ExactFunctor.of (VaryingRing.extension C τ b)).obj.Additive := by
    change (VaryingRing.extension C τ b).Additive
    infer_instance
  have : (ExactFunctor.of (VaryingRing.extension C τ k)).obj.Additive := by
    change (VaryingRing.extension C τ k).Additive
    infer_instance
  have : (ExactFunctor.of (VaryingRing.pull C τ r)).obj.Additive := by
    change (VaryingRing.pull C τ r).Additive
    infer_instance
  have hl := clopen_composite_localized D
    (ExactFunctor.of (VaryingRing.extension C τ i))
    (ExactFunctor.of (VaryingRing.pull C τ p))
    (ExactFunctor.of (VaryingRing.pull C τ a))
    (ExactFunctor.of (VaryingRing.pull C τ s))
    (ExactFunctor.of (VaryingRing.extension C τ s))
    (ExactFunctor.of (VaryingRing.extension C τ b))
    (ExactFunctor.of (VaryingRing.extension C τ k))
    (ExactFunctor.of (VaryingRing.pull C τ r))
    (VaryingRing.moduleBeta C τ a b i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip).hom
    (VaryingRing.modulePi C τ s)
    ((VaryingRing.moduleJComp C τ s b).hom ≫
      (VaryingRing.moduleJCongr C τ (squareLift_fst k r p i h)).hom)
    ((VaryingRing.moduleGComp C τ s a).inv ≫
      (eqToIso (congrArg (VaryingRing.pull C τ) (squareLift_snd k r p i h))).hom)
  have ho : VaryingRing.moduleAlpha C τ k r p i h =
      clopenMateComposite _ _ _ _ _ _ _ _
        (VaryingRing.moduleBeta C τ a b i p pullback.condition.symm
          (IsPullback.of_hasPullback p i).flip).hom
        (VaryingRing.modulePi C τ s)
        ((VaryingRing.moduleJComp C τ s b).hom ≫
          (VaryingRing.moduleJCongr C τ (squareLift_fst k r p i h)).hom)
        ((VaryingRing.moduleGComp C τ s a).inv ≫
          (eqToIso (congrArg (VaryingRing.pull C τ) (squareLift_snd k r p i h))).hom) :=
    expanded_clopen_composite _ _ _ _ _ _ _ _ _ _ _ _
  simp only [ExactFunctor.of_fst] at hl
  rw [← ho] at hl
  apply HEq.trans hl.heq
  have ht := clopen_composite_heq
    (VaryingRing.J C τ i) (SemilinearProperOpen.J C τ i)
    (VaryingRing.G C τ p) (SemilinearProperOpen.P C τ p)
    (VaryingRing.G C τ a) (SemilinearProperOpen.P C τ a)
    (VaryingRing.G C τ s) (SemilinearProperOpen.P C τ s)
    (VaryingRing.J C τ s) (SemilinearProperOpen.J C τ s)
    (VaryingRing.J C τ b) (SemilinearProperOpen.J C τ b)
    (VaryingRing.J C τ k) (SemilinearProperOpen.J C τ k)
    (VaryingRing.G C τ r) (SemilinearProperOpen.P C τ r)
    _ _ _ _ _ _ _ _
    (SemilinearProperOpen.J_eq C τ i).symm (SemilinearProperOpen.P_eq C τ p).symm
    (SemilinearProperOpen.P_eq C τ a).symm (SemilinearProperOpen.P_eq C τ s).symm
    (SemilinearProperOpen.J_eq C τ s).symm (SemilinearProperOpen.J_eq C τ b).symm
    (SemilinearProperOpen.J_eq C τ k).symm (SemilinearProperOpen.P_eq C τ r).symm
    (system_beta_localized C τ a b i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip)
    (system_projector_localized C τ s c.ι hc)
    (system_open_cell_localized C τ s b k (squareLift_fst k r p i h))
    (system_pull_cell_localized C τ s a r (squareLift_snd k r p i h))
  apply ht.trans
  exact (expanded_clopen_composite _ _ _ _ _ _ _ _ _ _ _ _).symm.heq

end AlgebraicGeometry.ProEtale.AmbientClopen
