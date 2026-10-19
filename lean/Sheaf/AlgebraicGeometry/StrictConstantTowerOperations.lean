/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N4 and J7
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Strict constant-coefficient tower operations

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-strict-constant-tower-operations).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

-- These elementary factorization calculations follow the proved helpers of
-- ProEtaleRingSheafChangeAdjunction, without importing its unrelated comparisons.
private theorem exactSquare_factorsh
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) (L' : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : G ⋙ L' ≅ L ⋙ H) (K : HomotopyCategory A (.up ℤ)) :
    ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso L H).hom.app
          (DerivedCategory.Qh.obj K) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory s.hom (.up ℤ)).app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fach L H K
  have h₂ := Functor.mapDerivedCategoryCompIso_fach G L' K
  have h₃ := Functor.mapDerivedCategoryNatIso_fach s K
  apply (cancel_mono (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁, h₃, ← h₂]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hc : DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [hc, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homotopy_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : HomotopyCategory B (.up ℤ)) :
    (mateEquiv (adj.mapHomotopyCategory (.up ℤ)) (adj'.mapHomotopyCategory (.up ℤ))
      (TwoSquare.mk _ _ _ _
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom ≫
          NatTrans.mapHomotopyCategory s.hom (.up ℤ) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv))).app K =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Functor.mapHomologicalComplexCompIso]
  simp only [ NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  simp only [Functor.id_obj, NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, NatIso.mapHomologicalComplex_inv_app_f, Iso.refl_inv,
    Functor.map_comp, HomologicalComplex.id_f, Category.comp_id, Category.assoc,
    Functor.comp_map]
  change adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (𝟙 (L'.obj (G.obj (R.obj (K.X n))))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (𝟙 (H.obj (L.obj (R.obj (K.X n))))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) =
    𝟙 _ ≫ adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [R'.map_id, Category.id_comp, Category.id_comp]

private theorem derived_mate_factorsh
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : HomotopyCategory B (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
            Functor.mapDerivedCategoryNatIso s ≪≫
            Functor.mapDerivedCategoryCompIso L H).hom)).app (DerivedCategory.Qh.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactorsh.hom.app K) =
    G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory
            (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app K) ≫
      R'.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj K) := by
  rw [← homotopy_mate adj adj' s K]
  exact Adjunction.derived_mateEquiv_app_fac
    (adj.mapHomotopyCategory (.up ℤ)) (adj'.mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso A (.up ℤ)) (HomotopyCategory.quasiIso B (.up ℤ))
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit
    L'.mapDerivedCategoryFactorsh.hom R'.rightDerivedFunctorUnit
    G.mapDerivedCategoryFactorsh.hom H.mapDerivedCategoryFactorsh.hom
    (TwoSquare.mk _ _ _ _
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory s.hom (.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv))
    (TwoSquare.mk _ _ _ _
      ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso L H).hom)
    K (exactSquare_factorsh L L' G H s _)


private theorem adjunct_comp_comparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ R)
    (e : Rf ⋙ Rg ≅ R) {A : C} {B : D} {T : E}
    (h : A ⟶ Rg.obj B) (k : B ⟶ Rf.obj T) :
    (adj.homEquiv A T).symm (h ≫ Rg.map k ≫ e.hom.app T) =
      ((conjugateEquiv (adjg.comp adjf) adj).symm e.hom).app A ≫
        Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k := by
  apply (adj.homEquiv A T).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  change _ = (adj.unit.app A ≫ R.map _) ≫ R.map _
  rw [← unit_conjugateEquiv_symm (adjg.comp adjf) adj e.hom A,
    Category.assoc, ← e.hom.naturality]
  conv_rhs => rw [← Category.assoc]
  change _ = ((adjg.comp adjf).homEquiv A T)
    (Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k) ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _) ≫ _
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Category.assoc]

variable (B : Type (u + 1)) [CommRing B]

/-- The existing constant-sheaf construction in the site's coefficient universe.
Source: Stacks, Tag 0H7J (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev coefficients (X : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of B)

/-- Modules over the actual constant ring sheaf. Source: Stacks, Tags 098K and 09AE
(blueprint: def-cbc-strict-constant-tower-operations). -/
abbrev Modules (X : Scheme.{u}) :=
  Scheme.proEtaleRingModules X ((coefficients B X))

/-- The module category is Grothendieck abelian at the site's original universes.
Source: Stacks, Tag 079P (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modules_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Modules B X) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u,
      u + 1}
    (Scheme.ProEt.topology X) (coefficients B X)).1

/-- Strict inverse systems, with index `n` representing level `n+1`.
Source: blueprint strict-tower refinement of Tag 0F7B
(blueprint: def-cbc-strict-constant-tower-operations). -/
abbrev Towers (X : Scheme.{u}) := ℕᵒᵖ ⥤ Modules B X

/-- Standard unbounded localization of the strict tower category.
Source: Stacks, Tag 05RU (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towers_hasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory (Towers B X) := HasDerivedCategory.standard _

/-- The ordinary unbounded derived category of strict towers.
Source: Stacks, Tag 05RU (blueprint: def-cbc-strict-constant-tower-operations). -/
abbrev Derived (X : Scheme.{u}) := DerivedCategory (Towers B X)

/-- Constant coefficients pull back canonically for arbitrary rings, including infinite ones.
Source: Stacks, Tag 0H7J and the blueprint's first proof step
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: maps out of a constant sheaf are maps out of its constant presheaf. Compose
this universal property with the inverse-image adjunction. The resulting comparison
preserves constant sections and is inverse to the canonical constant-section map. -/
theorem constantRing_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B)) := by
  let A := CommRingCat.of B
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let hGT := hT.isTerminalObj (Scheme.proEtaleBaseChange f)
  let adjY := constantSheafAdj (Scheme.ProEt.topology Y) CommRingCat.{u + 1} hT
  let adjX := constantSheafAdj (Scheme.ProEt.topology X) CommRingCat.{u + 1} hGT
  let adj := (adjY.comp (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})).ofNatIsoRight
    ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (op T))
  have he : Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A =
      (adj.leftAdjointUniq adjX).hom.app A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})).homEquiv _ _
      (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
          (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{u + 1} hT).comp
      (sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1})).homEquiv _ _
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
        (((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- The canonical constant-ring identification, retaining its constant-section map.
Source: Stacks, Tag 0H7J (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def constantRingIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      ((coefficients B Y)) ≅ (coefficients B X) :=
  @asIso _ _ _ _ (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))
    (constantRing_isIso B f)

/-- Exact module inverse image through the canonical constant-ring identification.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def modulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules B Y ⥤ Modules B X :=
  Scheme.proEtaleRingModulePullback f ((coefficients B Y))
    ((coefficients B X)) (constantRingIso B f)

/-- Module direct image with the adjoint constant-ring map.
Source: Stacks, Tag 03DA (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules B X ⥤ Modules B Y :=
  Scheme.proEtaleRingModuleDirectImage f ((coefficients B Y))
    ((coefficients B X)) (constantRingIso B f)

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modulePullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modulePullback B f).Additive :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).1

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance moduleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleDirectImage B f).Additive :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.1

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modulePullback_finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (modulePullback B f) :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.2.1

/-- The recorded module-operation instance, specialized to canonical constant coefficients.
Source: Stacks, Tag 03EK (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance modulePullback_finiteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (modulePullback B f) :=
  (Scheme.proEtaleRingModuleOperations_properties f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).2.2.2.1

/-- Termwise inverse image on strict towers.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev towerPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B Y) (Modules B X)).obj (modulePullback B f)

/-- Termwise direct image on strict towers.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev towerDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B X) (Modules B Y)).obj (moduleDirectImage B f)

/-- Tower complexes admit K-injective resolutions, without a uniform levelwise bound.
Source: blueprint, first proof step, Stacks, Tags 079B and 079P
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: the module category is Grothendieck abelian. Filtered colimits of towers are
exact pointwise. If H is a separator of modules, the coproduct over n of the free
diagrams on H is a separator of towers: transpose a detecting map at an index
under the evaluation adjunction. Thus towers are Grothendieck abelian and the
existing general K-injective resolution theorem applies. -/
theorem towers_hasKInjectiveResolutions (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasKInjectiveResolutions (Towers B X) := by
  let M := Modules B X
  let H := separator M
  have hH := isSeparator_separator M
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint M j).obj H) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hH.def
    intro a
    let ad := evaluationAdjunctionRight M j
    apply (ad.homEquiv H F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((ad.homEquiv H F).symm a)
    exact (ad.homEquiv_naturality_right_symm a f).trans
      (h.trans (ad.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (Towers B X) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{u + 1, u + 1} (Towers B X) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u + 1, u + 1} (Towers B X) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : IsGrothendieckAbelian.{u + 1} (Towers B X) := {}
  infer_instance

/-- K-injective existence as an instance. Source: Stacks, Tag 079P
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towers_kInjective (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasKInjectiveResolutions (Towers B X) :=
  towers_hasKInjectiveResolutions B X

/-- Termwise exactness uses the levelwise kernels and cokernels of strict diagrams.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations).
Proof: evaluate each finite limit and colimit at an index. The module inverse image
is exact, so the pointwise comparison is invertible. Evaluation jointly reflects
isomorphisms of strict diagrams, proving both claims. -/
theorem towerPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (towerPullback B f) ∧
      PreservesFiniteColimits (towerPullback B f) := by
  constructor
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Left exactness on strict diagrams. Source: blueprint, first proof step
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towerPullback_finiteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (towerPullback B f) := (towerPullback_exact B f).1

/-- Right exactness on strict diagrams. Source: blueprint, first proof step
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable instance towerPullback_finiteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (towerPullback B f) := (towerPullback_exact B f).2

/-- Exact inverse image on the unbounded derived strict-tower category.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def G {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived B Y ⥤ Derived B X :=
  (towerPullback B f).mapDerivedCategory

/-- Total right derived termwise direct image.
Source: blueprint, first proof step (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def R {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived B X ⥤ Derived B Y :=
  (towerDirectImage B f).rightDerivedFunctor

/-- The derived adjunction induced from the normalized sheaf adjunction, termwise.
Source: Stacks, Tag 0DVC (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : G B f ⊣ R B f :=
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
    ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ)

/-- Evaluation of the derived strict tower, keeping its actual derived-category source.
Source: blueprint, evaluation clauses (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable abbrev ev (X : Scheme.{u}) (n : ℕ) :
    Derived B X ⥤ DerivedCategory (Modules B X) :=
  ((evaluation ℕᵒᵖ (Modules B X)).obj (op n)).mapDerivedCategory


/-- Compatibility of the canonical constant-section identifications with composition.
Source: Stacks, Tag 0H7J (blueprint: def-cbc-strict-constant-tower-operations).
Proof: transpose both maps under inverse image. On every constant scalar both maps
are the same constant section; the sheafification universal property gives equality. -/
theorem constantRingIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    constantRingIso B (f ≫ g) = Scheme.proEtaleRingCompositeCoefficients f g
      (coefficients B Z) (coefficients B Y) (coefficients B X)
      (constantRingIso B g) (constantRingIso B f) := by
  apply Iso.ext
  let A := CommRingCat.of B
  change Scheme.proEtaleConstantInverseImageMap (f ≫ g) CommRingCat.{u + 1} A =
    (Scheme.proEtaleRingInverseImageComp f g).hom.app (coefficients B Z) ≫
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (Scheme.proEtaleConstantInverseImageMap g CommRingCat.{u + 1} A) ≫
      Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have hρ : Scheme.proEtaleConstantDirectImageMap (f ≫ g) CommRingCat.{u + 1} A =
      Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫
            e.hom.app ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
    apply ((sheafificationAdjunction (Scheme.ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj A) _).injective
    rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right]
    rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext U
    have hf := Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj A)
          ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
    have hfU := congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange g).op.obj U)) hf
    change (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        ((Scheme.proEtaleBaseChange g).op.obj U) ≫
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
        ((Scheme.proEtaleBaseChange g).op.obj U) =
          (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
            ((Scheme.proEtaleBaseChange f).op.obj ((Scheme.proEtaleBaseChange g).op.obj U)) at hfU
    change (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj U) =
      ((toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
          ((Scheme.proEtaleBaseChange g).op.obj U) ≫
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
          ((Scheme.proEtaleBaseChange g).op.obj U)) ≫
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
              ((MorphismProperty.Over.pullbackComp
                (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    rw [hfU]
    have h := (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    change 𝟙 A ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  change ((Scheme.proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1}).homEquiv _ _).symm _ = _
  rw [hρ]
  exact adjunct_comp_comparison (Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1})
    (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})
    (Scheme.proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1}) e
    (Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A)
    (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A)

/-- Fibre-product pasting uniquely normalizes ordinary direct-image composition.
Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: evaluate both direct images on a test object. Restriction along the canonical
fibre-product pasting isomorphism gives the displayed map and its inverse. These are
linear by preservation of constant sections and natural by the universal property
of pullbacks. Equality on all sections proves uniqueness. -/
theorem moduleRComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : moduleDirectImage B f ⋙ moduleDirectImage B g ≅ moduleDirectImage B (f ≫ g),
      ∀ (N : Modules B X) (U : Z.ProEt)
        (m : ((moduleDirectImage B f ⋙ moduleDirectImage B g).obj N).val.obj (op U)),
        (d.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m := by
  obtain ⟨_, _, _, _, _, _, d, hd, _⟩ :=
    Scheme.proEtaleRingDerivedPullbackComposition f g
      (coefficients B Z) (coefficients B Y) (coefficients B X)
      (constantRingIso B g) (constantRingIso B f) (constantRingIso B (f ≫ g))
      (constantRingIso_comp B f g)
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (he N U.unop m).trans (hd N U.unop m).symm

/-- The section-normalized direct-image compositor. Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleRComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleDirectImage B f ⋙ moduleDirectImage B g ≅ moduleDirectImage B (f ≫ g) :=
  Classical.choose (moduleRComp_existsUnique B f g)

/-- Pullback composition is the unit-preserving conjugate of fibre-product pasting.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback B (f ≫ g) ≅ modulePullback B g ⋙ modulePullback B f :=
  (Adjunction.leftAdjointCompIso
    (Scheme.proEtaleRingModuleAdjunction g (coefficients B Z)
      (coefficients B Y) (constantRingIso B g))
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f))
    (Scheme.proEtaleRingModuleAdjunction (f ≫ g) (coefficients B Z)
      (coefficients B X) (constantRingIso B (f ≫ g))) (moduleRComp B f g)).symm

/-- Strict tower pullback composition is the actual whiskered module comparison.
Source: Stacks, Tag 0D6D
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def towerGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    towerPullback B (f ≫ g) ≅ towerPullback B g ⋙ towerPullback B f :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleGComp B f g)) ≪≫
    Functor.whiskeringRightObjCompIso (modulePullback B g) (modulePullback B f)

/-- The pullback compositor descends from the actual termwise module compositor.
Source: Stacks, Tag 0D6D (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def gComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G B (f ≫ g) ≅ G B g ⋙ G B f :=
  Functor.mapDerivedCategoryNatIso (towerGComp B f g) ≪≫
    Functor.mapDerivedCategoryCompIso (towerPullback B g) (towerPullback B f)

/-- The direct-image compositor is the conjugate for the composition adjunction.
Source: Stacks, Tags 0D6D and 07A7
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def rComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R B f ⋙ R B g ≅ R B (f ≫ g) :=
  conjugateIsoEquiv ((adj B g).comp (adj B f)) (adj B (f ≫ g)) (gComp B f g)

/-- The identity direct image is the sectionwise pullback-identity comparison.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations).
Proof: the inverse base-change identity sends U to U ×_X X by its graph. Restrict
sections along this map. It preserves constant scalar sections, so is linear. Its
inverse is restriction along the inverse graph. Sections determine a unique map. -/
theorem moduleRId_existsUnique (X : Scheme.{u}) :
    ∃! e : moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X),
      ∀ (M : Modules B X) (U : X.ProEt)
        (m : ((moduleDirectImage B (𝟙 X)).obj M).val.obj (op U)),
        (e.hom.app M).val.app (op U) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op m := by
  let A := CommRingCat.of B
  let e := Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
      (Scheme.ProEt.topology X)
  have hρ : Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A =
      e.inv.app ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
    apply ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj A) _).injective
    rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_apply]
    apply NatTrans.ext
    funext U
    change (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((Scheme.proEtaleBaseChange (𝟙 X)).op.obj U) =
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app U ≫
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op
    have h := (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op
    change 𝟙 A ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  let i := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X
  let S := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
  let φ : S ⟶ ((Scheme.proEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)).obj S :=
    ⟨Functor.whiskerRight (Scheme.proEtaleRingDirectImageMap (𝟙 X)
      (coefficients B X) (coefficients B X) (constantRingIso B (𝟙 X))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hφ : Scheme.proEtaleRingDirectImageMap (𝟙 X)
      (coefficients B X) (coefficients B X) (constantRingIso B (𝟙 X)) =
        Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A := by
    exact Equiv.apply_symm_apply
      ((Scheme.proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).homEquiv _ _)
      (Scheme.proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A)
  have he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans i.inv
      RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)).app S = 𝟙 S := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext a
    change (coefficients B X).obj.map (i.inv.app U.unop).op
      (((Scheme.proEtaleRingDirectImageMap (𝟙 X) (coefficients B X) (coefficients B X)
        (constantRingIso B (𝟙 X))).hom.app U) a) = a
    rw [hφ, hρ]
    change ((coefficients B X).obj.map (i.inv.app U.unop).op)
      ((coefficients B X).obj.map (i.hom.app U.unop).op a) = a
    change (((coefficients B X).obj.map (i.hom.app U.unop).op ≫
      (coefficients B X).obj.map (i.inv.app U.unop).op) a) = a
    rw [← Functor.map_comp, ← op_comp, i.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
    rfl
  let : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ X)).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) :=
    Functor.isContinuous_id (Scheme.ProEt.topology X)
  let d : moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X) :=
    SheafOfModules.pushforwardCongr₂ (φ := φ) i.symm he ≪≫ SheafOfModules.pushforwardId S
  have hd : ∀ (M : Modules B X) (U : X.ProEt)
      (m : ((moduleDirectImage B (𝟙 X)).obj M).val.obj (op U)),
      (d.hom.app M).val.app (op U) m = M.val.map (i.inv.app U).op m := by
    intro M U m
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (hd' M U.unop m).trans (hd M U.unop m).symm

/-- The section-normalized identity direct-image comparison.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def moduleRId (X : Scheme.{u}) :
    moduleDirectImage B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Classical.choose (moduleRId_existsUnique B X)

/-- The inverse-image identity is the normalized conjugate of the sectionwise identity.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def gId (X : Scheme.{u}) : G B (𝟙 X) ≅ 𝟭 (Derived B X) :=
  Functor.mapDerivedCategoryNatIso
    (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (Adjunction.leftAdjointIdIso
        (Scheme.proEtaleRingModuleAdjunction (𝟙 X) (coefficients B X)
          (coefficients B X) (constantRingIso B (𝟙 X))) (moduleRId B X))) ≪≫
      Functor.whiskeringRightObjIdIso) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The normalized derived direct-image identity.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def rId (X : Scheme.{u}) : R B (𝟙 X) ≅ 𝟭 (Derived B X) :=
  (conjugateIsoEquiv Adjunction.id (adj B (𝟙 X)) (gId B X)).symm


/-- Evaluation commutes with strict termwise inverse image.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: both object maps evaluate the same strict tower at n and apply the same
module functor. Their maps are the same evaluated natural transformations. -/
theorem evaluationPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    towerPullback B f ⋙ (evaluation ℕᵒᵖ (Modules B X)).obj (op n) =
      (evaluation ℕᵒᵖ (Modules B Y)).obj (op n) ⋙ modulePullback B f := by
  rfl

/-- The evaluation/pullback comparison induced by the actual termwise equality.
Source: blueprint evaluation normalization
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def evalG {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    G B f ⋙ ev B X n ≅ ev B Y n ⋙ (modulePullback B f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
  Functor.mapDerivedCategoryNatIso (eqToIso (evaluationPullback B f n)) ≪≫
  Functor.mapDerivedCategoryCompIso _ _

/-- The direct-image evaluation map is its specified adjunction mate.
Source: Stacks, Tags 07A7 and 0DVC
(blueprint: def-cbc-strict-constant-tower-operations). -/
noncomputable def evalR {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    R B f ⋙ ev B Y n ⟶ ev B X n ⋙ (moduleDirectImage B f).rightDerivedFunctor :=
  mateEquiv (adj B f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).mapDerivedCategoryRightDerivedAdjunction
    (evalG B f n).inv

private theorem evaluation_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv
      ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
        (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ)
      (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
        (coefficients B X) (constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (eqToIso (evaluationPullback B f n)).inv)).natTrans =
        𝟙 ((evaluation ℕᵒᵖ (Modules B X)).obj (op n) ⋙ moduleDirectImage B f) := by
  apply NatTrans.ext
  funext T
  change (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).unit.app
        ((moduleDirectImage B f).obj (T.obj (op n))) ≫
      (moduleDirectImage B f).map
        ((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
          (coefficients B X) (constantRingIso B f)).counit.app (T.obj (op n))) = 𝟙 _
  exact (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).right_triangle_components _

/-- This normalized mate is invertible, without a uniform lower bound.
Source: blueprint evaluation proof step, and Stacks, Tag 08BJ
(blueprint: def-cbc-strict-constant-tower-operations).
Proof: a K-injective strict tower evaluates to a K-injective complex: evaluation
has an exact left adjoint given by sums over the index arrows. On such a
representative both direct images give the identical evaluated complex.
The homotopy adjunction is termwise, so the derived Hom bijection identifies
this equality with the displayed mate, including its unit and counit. -/
theorem evalR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (evalR B f n) := by
  let L := towerPullback B f
  let L' := modulePullback B f
  let P := towerDirectImage B f
  let P' := moduleDirectImage B f
  let E := (evaluation ℕᵒᵖ (Modules B Y)).obj (op n)
  let E' := (evaluation ℕᵒᵖ (Modules B X)).obj (op n)
  have : PreservesFiniteLimits L := towerPullback_finiteLimits B f
  have : PreservesFiniteColimits L := towerPullback_finiteColimits B f
  have : PreservesFiniteLimits L' := modulePullback_finiteLimits B f
  have : PreservesFiniteColimits L' := modulePullback_finiteColimits B f
  let a : L ⊣ P := (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ
  let a' : L' ⊣ P' := Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
    (coefficients B X) (constantRingIso B f)
  let s : E ⋙ L' ≅ L ⋙ E' := (eqToIso (evaluationPullback B f n)).symm
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  have hfac := derived_mate_factorsh a a' s H
  let hEval : CochainComplex.IsKInjective
      ((E'.mapHomologicalComplex (.up ℤ)).obj I) :=
    tower_evaluation_isKInjective (Modules B X) I (op n)
  have hP : IsIso (P.rightDerivedFunctorUnit.app H) := inferInstance
  have hP' : IsIso (P'.rightDerivedFunctorUnit.app
      ((E'.mapHomotopyCategory (.up ℤ)).obj H)) := by
    change IsIso (P'.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((E'.mapHomologicalComplex (.up ℤ)).obj I)))
    infer_instance
  have hm : (mateEquiv a a' (TwoSquare.mk _ _ _ _ s.hom)).natTrans =
      𝟙 (E' ⋙ P') := evaluation_mate B f n
  have hs : ((Functor.mapDerivedCategoryCompIso E L').symm ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫
      Functor.mapDerivedCategoryCompIso L E').hom = (evalG B f n).inv := by
    dsimp only [s, evalG]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rfl
  have hh : IsIso
      ((NatTrans.mapHomotopyCategory
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app H) := by
    rw [hm]
    change IsIso ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (𝟙 (E' ⋙ P')) (.up ℤ)).app I))
    have hId : (NatTrans.mapHomologicalComplex (𝟙 (E' ⋙ P')) (.up ℤ)).app I =
        𝟙 _ := by ext k; rfl
    rw [hId, CategoryTheory.Functor.map_id]
    infer_instance
  have hcomp : IsIso (E.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app H) ≫
      (evalR B f n).app (DerivedCategory.Qh.obj H) ≫
        P'.rightDerivedFunctor.map (E'.mapDerivedCategoryFactorsh.hom.app H)) := by
    change IsIso (E.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app H) ≫
      (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        a'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (evalG B f n).inv)).natTrans.app
          (DerivedCategory.Qh.obj H) ≫
        P'.rightDerivedFunctor.map (E'.mapDerivedCategoryFactorsh.hom.app H))
    rw [← hs, hfac]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance
    (@IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hcomp)

end AlgebraicGeometry.ProEtale.StrictTower
