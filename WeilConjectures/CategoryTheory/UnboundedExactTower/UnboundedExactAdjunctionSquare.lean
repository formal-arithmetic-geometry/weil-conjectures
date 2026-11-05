/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.RingedToposMorphism
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Exact unbounded adjunctions, strict towers, and square mates

Source: Stacks Project, Derived Categories, Tags 0DVC, 0FND, 08BJ and 070I;
Cohomology on Sites, Tag 07A7; the constant/evaluation application is agent supplied
(blueprint: lem-sbc-unbounded-exact-adjunction-square).

The index `op n` denotes positive level `n + 1`. All comparisons below are constructed
from the specified ordinary adjunction and exact-localization comparisons. In particular,
no arbitrary natural isomorphism or faithful derived evaluation is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u vA uA vB uB wA wB wTA wTB wA' wB' wTA' wTB'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.UnboundedExactTower

/-- The existing Grothendieck-category K-injective resolution construction for module
sheaves. Source: Stacks 079P, 07A5
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
instance moduleResolutions
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R) :=
  letI := SheafOfModules.isGrothendieckAbelian R
  inferInstance

section Comparisons

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {F} {G : A ⥤ B} [G.Additive]
  [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]

/-- The canonical cochain-level unit of the existing total right derived functor.
It is obtained from its homotopy-level unit using the quotient factorization isomorphisms.
Source: Stacks 070K (blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def cochainUnit (G : A ⥤ B) [G.Additive] (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app I)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] in
private theorem cochain_counit (a : F ⊣ G) (I : CochainComplex A ℤ) :
    F.mapDerivedCategory.map (cochainUnit G I) ≫
        a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient A (.up ℤ)).obj I)
  change F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app _) ≫
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app _ =
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫ _ at h
  simp only [cochainUnit, Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.map_comp, Category.assoc] at h ⊢
  simp only [Quotient.lift.isLift_hom] at h ⊢
  repeat erw [Functor.map_id] at h
  repeat erw [Functor.map_id]
  repeat erw [Category.id_comp] at h
  repeat erw [Category.id_comp]
  exact h

end Comparisons

section Square

universe uA' vA' uB' vB'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wTA'} (ℕᵒᵖ ⥤ A')] [HasDerivedCategory.{wTB'} (ℕᵒᵖ ⥤ B')]
  (F : B ⥤ A) (F' : B' ⥤ A') (g : B ⥤ B') (h : A ⥤ A')
  [F.Additive] [F'.Additive] [g.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

/-- Localize the given inverse-image composition comparison with the specified
composition isomorphisms. Source: Stacks 015F and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def localizedSquare (θ : g ⋙ F' ≅ F ⋙ h) :
    g.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ h.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso g F').symm ≪≫
    Functor.mapDerivedCategoryNatIso θ ≪≫ Functor.mapDerivedCategoryCompIso F h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A')] [HasDerivedCategory (ℕᵒᵖ ⥤ B')] in
private theorem localizedSquare_fac (θ : g ⋙ F' ≅ F ⋙ h)
    (M : CochainComplex B ℤ) :
    (localizedSquare F F' g h θ).hom.app (DerivedCategory.Q.obj M) ≫
        h.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app M) ≫
        h.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
      F'.mapDerivedCategory.map (g.mapDerivedCategoryFactors.hom.app M) ≫
        F'.mapDerivedCategoryFactors.hom.app ((g.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app M) := by
  simp only [localizedSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fac F h M
  have hc' := Functor.mapDerivedCategoryCompIso_fac g F' M
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ h))
      (.up ℤ)).hom.app M = 𝟙 _ := rfl
  have hi' : (Functor.mapHomologicalComplexCompIso (Iso.refl (g ⋙ F'))
      (.up ℤ)).hom.app M = 𝟙 _ := rfl
  erw [hi, Functor.map_id, Category.comp_id] at hc
  erw [hi', Functor.map_id, Category.comp_id] at hc'
  erw [hc, Functor.mapDerivedCategoryNatIso_fac]
  erw [← hc']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

variable {F F' g h} {G : A ⥤ B} {G' : A' ⥤ B'} [G.Additive] [G'.Additive]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A')] [HasDerivedCategory (ℕᵒᵖ ⥤ B')]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')] in
private theorem localized_mate_cochain (a : F ⊣ G) (a' : F' ⊣ G')
    (θ : g ⋙ F' ≅ F ⋙ h) (I : CochainComplex A ℤ) :
    g.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        g.mapDerivedCategory.map (cochainUnit G I) ≫
        (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          a'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app
            (DerivedCategory.Q.obj I) ≫
        G'.rightDerivedFunctor.map (h.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans (.up ℤ)).app I) ≫
        cochainUnit G' ((h.mapHomologicalComplex (.up ℤ)).obj I) := by
  apply (a'.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [a'.mapDerivedCategoryRightDerivedAdjunction.counit.naturality]
  have hm := mateEquiv_counit a.mapDerivedCategoryRightDerivedAdjunction
    a'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom) (DerivedCategory.Q.obj I)
  erw [reassoc_of% hm]
  erw [reassoc_of% (localizedSquare F F' g h θ).hom.naturality (cochainUnit G I)]
  simp only [Functor.id_map]
  rw [← h.mapDerivedCategory.map_comp_assoc, cochain_counit]
  simp only [Functor.map_comp, Category.assoc]
  erw [h.mapDerivedCategoryFactors_hom_naturality]
  erw [reassoc_of% localizedSquare_fac F F' g h θ
    ((G.mapHomologicalComplex (.up ℤ)).obj I)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [cochain_counit]
  erw [reassoc_of% F'.mapDerivedCategoryFactors_hom_naturality
    ((NatTrans.mapHomologicalComplex
      (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans (.up ℤ)).app I)]
  simp only [← Functor.map_comp]
  congr 2
  ext n
  exact (mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ θ.hom) (I.X n)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A')] [HasDerivedCategory (ℕᵒᵖ ⥤ B')]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')] in
/-- The canonical derived square mate is represented by the ordinary mate on complexes.
Source: Stacks 070I, 08BJ and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square).

Transpose by the derived adjunction, apply its counit normalization, and use the
localization factorization of the inverse-image square. The ordinary mate counit
identity in each degree gives the resulting equality. -/
theorem localized_mate_cochain_normalization (a : F ⊣ G) (a' : F' ⊣ G')
    (θ : g ⋙ F' ≅ F ⋙ h) (I : CochainComplex A ℤ) :
    g.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        g.mapDerivedCategory.map (cochainUnit G I) ≫
        (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          a'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app
            (DerivedCategory.Q.obj I) ≫
        G'.rightDerivedFunctor.map (h.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans (.up ℤ)).app I) ≫
        cochainUnit G' ((h.mapHomologicalComplex (.up ℤ)).obj I) := by
  exact localized_mate_cochain a a' θ I

end Square

section ComparisonProofs

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  {F : B ⥤ A} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : A ⥤ B} [G.Additive] [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]

end ComparisonProofs

section EvaluationCube

universe uA' vA' uB' vB'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wTA'} (ℕᵒᵖ ⥤ A')] [HasDerivedCategory.{wTB'} (ℕᵒᵖ ⥤ B')]
  (F : B ⥤ A) (F' : B' ⥤ A') (g : B ⥤ B') (h : A ⥤ A')
  [F.Additive] [F'.Additive] [g.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

end EvaluationCube

end CategoryTheory.UnboundedExactTower
