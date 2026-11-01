/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.TotalSiteAugmentationData.TotalSiteInjectiveAugmentationExactness
public import Mathlib.Order.Fin.Basic
public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
public import WeilConjectures.CategoryTheory.FiniteOrderedCechSquare
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent

/-! # Section coordinates for the ordered relative-image Čech row

Source: Stacks Project, Tag 03AZ, row calculation; Tags 03FB and 03FC for
injective module presheaves, and Tags 01FJ–01FM for the ordered comparison.
(blueprint: new-finite-cover-row-sections)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

-- Preliminary concrete coordinates for the geometric descent calculation.
def finiteCoverTestObject (f : X ⟶ Y) (T : Y.Etale) (V : X.Opens) : X.Etale :=
  (MorphismProperty.Over.map (P := @Etale) ⊤ (show Etale V.ι by infer_instance)).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ (V.ι ≫ f)).obj T)

def finiteCoverTestObjectHom (f : X ⟶ Y) (T : Y.Etale)
    {V W : X.Opens} (h : V ≤ W) :
    finiteCoverTestObject f T V ⟶ finiteCoverTestObject f T W :=
  MorphismProperty.Over.homMk
    (pullback.map T.hom (V.ι ≫ f) T.hom (W.ι ≫ f)
      (𝟙 T.left) (X.homOfLE h) (𝟙 Y) (by simp) (by simp))
    (by simp [finiteCoverTestObject, Category.assoc])

def finiteCoverImageSectionsIso (f : X ⟶ Y) (V : X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (T : Y.Etale) :
    ((finiteCoverOpenImage B f V).obj M).obj.obj (Opposite.op T) ≅
      M.obj.obj (Opposite.op (finiteCoverTestObject f T V)) := by
  let T' := (MorphismProperty.Over.pullback @Etale ⊤ (V.ι ≫ f)).obj T
  let ev := sheafToPresheaf (V : Scheme).smallEtaleTopology (ModuleCat.{u + 1} B) ⋙
    (CategoryTheory.evaluation (V : Scheme).Etaleᵒᵖ (ModuleCat.{u + 1} B)).obj
      (Opposite.op T')
  exact ev.mapIso
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) V.ι inferInstance).app M)

theorem finiteCoverImageSectionsIso_naturality (f : X ⟶ Y) (V : X.Opens)
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)} (g : M ⟶ N)
    (T : Y.Etale) :
    (((finiteCoverOpenImage B f V).map g).hom.app (Opposite.op T)) ≫
        (finiteCoverImageSectionsIso B f V N T).hom =
      (finiteCoverImageSectionsIso B f V M T).hom ≫
        g.hom.app (Opposite.op (finiteCoverTestObject f T V)) := by
  exact congrArg (fun a ↦ a.hom.app
    (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ (V.ι ≫ f)).obj T)))
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) V.ι
      inferInstance).hom.naturality g)

private theorem finiteCoverRestriction_localization (f : X ⟶ Y)
    {V W : X.Opens} (h : V ≤ W)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (finiteCoverImageRestriction B f h).app M ≫
        (lowerStar (ModuleCat.{u + 1} B) (V.ι ≫ f)).map
          ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) V.ι
            inferInstance).hom.app M) =
      (lowerStar (ModuleCat.{u + 1} B) (W.ι ≫ f)).map
          ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) W.ι
            inferInstance).hom.app M) ≫
        (lowerStar (ModuleCat.{u + 1} B) (W.ι ≫ f)).map
          ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B)
            (X.homOfLE h) inferInstance).unit.app
              ((localizationRestriction (ModuleCat.{u + 1} B) W.ι inferInstance).obj M)) ≫
        (lowerStarComp (ModuleCat.{u + 1} B) (X.homOfLE h) (W.ι ≫ f)
          (V.ι ≫ f) (by simp)).hom.app
            ((localizationRestriction (ModuleCat.{u + 1} B) (X.homOfLE h)
              inferInstance).obj
                ((localizationRestriction (ModuleCat.{u + 1} B) W.ι inferInstance).obj M)) ≫
        (lowerStar (ModuleCat.{u + 1} B) (V.ι ≫ f)).map
          ((localizationRestrictionComp' (ModuleCat.{u + 1} B) (X.homOfLE h) W.ι
            V.ι (by simp)).inv.app M) := by
  let A := ModuleCat.{u + 1} B
  let k := X.homOfLE h
  let FW := lowerStar A (W.ι ≫ f)
  let FV := lowerStar A (V.ι ≫ f)
  let K := upperStar A k
  let KR := lowerStar A k
  let lW := upperStarIsoLocalizationRestriction A W.ι inferInstance
  let lV := upperStarIsoLocalizationRestriction A V.ι inferInstance
  let lK := upperStarIsoLocalizationRestriction A k inferInstance
  let t := upperStarComp A k W.ι V.ι (by simp [k])
  let lc := localizationRestrictionComp' A k W.ι V.ι (by simp [k])
  let sk := lowerStarComp A k (W.ι ≫ f) (V.ι ≫ f) (by simp [k])
  let G := (upperStar A W.ι).obj M
  let H := (localizationRestriction A W.ι inferInstance).obj M
  have hcomp := upperStarIsoLocalizationRestriction_comp A k W.ι V.ι (by simp [k]) M
  have ht : t.inv.app M ≫ lV.hom.app M =
      K.map (lW.hom.app M) ≫ lK.hom.app H ≫ lc.inv.app M := by
    rw [← cancel_epi (t.hom.app M)]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% hcomp]
    change lV.hom.app M = lV.hom.app M ≫ lc.hom.app M ≫ lc.inv.app M
    simp
  change (FW.map ((upperStarLowerStarAdjunction A k).unit.app G) ≫
      sk.hom.app (K.obj G) ≫ FV.map (t.inv.app M)) ≫ FV.map (lV.hom.app M) =
    FW.map (lW.hom.app M) ≫
      FW.map ((localizationRestrictionLowerStarAdjunction A k inferInstance).unit.app H) ≫
      sk.hom.app ((localizationRestriction A k inferInstance).obj H) ≫
      FV.map (lc.inv.app M)
  simp only [Category.assoc]
  rw [← FV.map_comp, ht, FV.map_comp, FV.map_comp]
  rw [← reassoc_of% (sk.hom.naturality (K.map (lW.hom.app M)))]
  have hu := (upperStarLowerStarAdjunction A k).unit.naturality (lW.hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← FW.map_comp_assoc, ← hu, FW.map_comp]
  rw [← reassoc_of% (sk.hom.naturality (lK.hom.app H))]
  have hu' : FW.map ((upperStarLowerStarAdjunction A k).unit.app H) ≫
      FW.map (KR.map (lK.hom.app H)) =
        FW.map ((localizationRestrictionLowerStarAdjunction A k inferInstance).unit.app H) := by
    rw [← FW.map_comp]
    exact congrArg FW.map ((upperStarLowerStarAdjunction A k).unit_leftAdjointUniq_hom_app
      (localizationRestrictionLowerStarAdjunction A k inferInstance) H)
  simp only [Category.assoc]
  rw [reassoc_of% hu']

theorem finiteCoverImageSectionsIso_restriction (f : X ⟶ Y)
    {V W : X.Opens} (h : V ≤ W)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (T : Y.Etale) :
    ((finiteCoverImageRestriction B f h).app M).hom.app (Opposite.op T) ≫
        (finiteCoverImageSectionsIso B f V M T).hom =
      (finiteCoverImageSectionsIso B f W M T).hom ≫
        M.obj.map (finiteCoverTestObjectHom f T h).op := by
  have hs := congrArg (fun a ↦ a.hom.app (Opposite.op T))
    (finiteCoverRestriction_localization B f h M)
  change _ ≫ ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) V.ι
    inferInstance).hom.app M).hom.app
      (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ (V.ι ≫ f)).obj T)) =
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) W.ι
      inferInstance).hom.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ (W.ι ≫ f)).obj T)) ≫ _
  simp only [
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app, lowerStarComp_hom_app_hom_app,
    localizationRestrictionLowerStarAdjunction_unit_app_hom_app',
    localizationRestriction_obj_obj_map,
    localizationRestrictionComp', Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Iso.symm_inv, Quiver.Hom.unop_op,
    ← Functor.map_comp, ← op_comp] at hs
  rw [hs]
  congr 1
  apply congrArg M.obj.map
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  change @Eq (pullback T.hom (V.ι ≫ f) ⟶ pullback T.hom (W.ι ≫ f)) _ _
  dsimp [finiteCoverTestObjectHom, MorphismProperty.Over.mapPullbackAdj_counit_app,
    MorphismProperty.Over.mapComp_hom_app_left]
  apply pullback.hom_ext <;> simp [Category.assoc]
  all_goals exact Category.id_comp _


/-- The pullbacks of open subobjects along an etale test object form a functor.
Source: Stacks Project, Tag 03AZ, relative row calculation.
(blueprint: new-finite-cover-row-sections) -/
def finiteCoverTestObjectFunctor (f : X ⟶ Y) (T : Y.Etale) : X.Opens ⥤ X.Etale where
  obj V := finiteCoverTestObject f T V
  map h := finiteCoverTestObjectHom f T (leOfHom h)
  map_id V := by
    apply MorphismProperty.Over.Hom.ext
    change @Eq (pullback T.hom (V.ι ≫ f) ⟶ pullback T.hom (V.ι ≫ f)) _ _
    apply pullback.hom_ext <;> simp [finiteCoverTestObjectHom]
    all_goals exact Category.id_comp _
  map_comp g h := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;> simp [finiteCoverTestObjectHom, Category.assoc]

/-- Sections on the inverse images of opens of X in X times_Y T.
Source: Stacks Project, Tag 03AZ.
(blueprint: new-finite-cover-row-sections) -/
def finiteCoverSectionPresheaf (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u + 1} B :=
  (finiteCoverTestObjectFunctor f T).op ⋙ M.obj

/-- Finite biproducts of section coefficients exist, including empty index sets.
Source: Stacks Project, Tag 01FJ, ordered Cech terms.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverSectionBiproducts (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) (p : ℕ) : HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (a k)))) := by
  infer_instance

/-- The increasing-tuple section group in horizontal degree p.
Source: Stacks Project, Tag 01FJ.
(blueprint: new-finite-cover-row-sections) -/
abbrev finiteCoverSectionTerm (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) (p : ℕ) : ModuleCat.{u + 1} B :=
  finiteOrderedCechTerm (finiteCoverSectionPresheaf B f T M) U
    (finiteCoverSectionBiproducts B f T M U) p

/-- The usual alternating deletion differential, now on section modules.
Source: Stacks Project, Tag 01FJ.
(blueprint: new-finite-cover-row-sections) -/
def finiteCoverSectionDifferential (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) (p : ℕ) :
    finiteCoverSectionTerm B f T M U p ⟶ finiteCoverSectionTerm B f T M U (p + 1) :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    finiteOrderedCechCoface (finiteCoverSectionPresheaf B f T M) U
      (finiteCoverSectionBiproducts B f T M U) p j

/-- Projection of the ordered differential is the alternating face sum.
Source: Stacks Project, Tag 01FJ. Project the defining biproduct lift; finite
sums and integer multiples commute with composition.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverSectionDifferential_π (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) (p : ℕ) (a : Fin (p + 2) ↪o Fin m) :
    finiteCoverSectionDifferential B f T M U p ≫
        biproduct.π (fun b : Fin (p + 2) ↪o Fin m ↦
          (finiteCoverSectionPresheaf B f T M).obj (op ((⨅ k, U (b k))))) a =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦
            (finiteCoverSectionPresheaf B f T M).obj (op ((⨅ k, U (b k)))))
            (j.succAboveOrderEmb.trans a) ≫
          (finiteCoverSectionPresheaf B f T M).map
            (homOfLE (le_iInf fun k ↦
              iInf_le (fun l ↦ U (a l)) (j.succAbove k))).op) := by
  simp only [finiteCoverSectionDifferential, Preadditive.sum_comp,
    Preadditive.zsmul_comp, finiteOrderedCechCoface, finiteCoverIntersection,
    Category.assoc, biproduct.lift_π]

/-- The component formula of the ordered differential on elements.
Source: Stacks Project, Tag 01FJ. Evaluate the preceding projection identity.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverSectionDifferential_π_apply (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) (p : ℕ)
    (x : finiteCoverSectionTerm B f T M U p) (a : Fin (p + 2) ↪o Fin m) :
    biproduct.π (fun b : Fin (p + 2) ↪o Fin m ↦
        (finiteCoverSectionPresheaf B f T M).obj (op ((⨅ k, U (b k))))) a
        (finiteCoverSectionDifferential B f T M U p x) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (finiteCoverSectionPresheaf B f T M).map
          (homOfLE (le_iInf fun k ↦
            iInf_le (fun l ↦ U (a l)) (j.succAbove k))).op
          (biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦
              (finiteCoverSectionPresheaf B f T M).obj (op ((⨅ k, U (b k)))))
            (j.succAboveOrderEmb.trans a) x) := by
  have h := ConcreteCategory.congr_hom (finiteCoverSectionDifferential_π B f T M U p a) x
  change _ = (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    (biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦
        (finiteCoverSectionPresheaf B f T M).obj (op ((⨅ k, U (b k)))))
        (j.succAboveOrderEmb.trans a) ≫
      (finiteCoverSectionPresheaf B f T M).map
        (homOfLE (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k))).op)).hom x at h
  simpa only [ModuleCat.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_neg,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.comp_apply] using! h

/-- Restriction from the total test object into the increasing singleton terms.
Source: Stacks Project, Tag 03AN.
(blueprint: new-finite-cover-row-sections) -/
def finiteCoverSectionAugmentation (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) :
    (finiteCoverSectionPresheaf B f T M).obj (op ⊤) ⟶
      finiteCoverSectionTerm B f T M U 0 :=
  biproduct.lift (fun a : Fin 1 ↪o Fin m ↦
    (finiteCoverSectionPresheaf B f T M).map
      (homOfLE (le_top : finiteCoverIntersection U a ≤ ⊤)).op)

/-- The section differential squares to zero by double-deletion cancellation.
Source: Stacks Project, Tag 01FJ.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverSectionDifferential_squared (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) (p : ℕ) :
    finiteCoverSectionDifferential B f T M U p ≫
      finiteCoverSectionDifferential B f T M U (p + 1) = 0 :=
  finiteOrderedCechDifferential_squared (finiteCoverSectionPresheaf B f T M) U
    (finiteCoverSectionBiproducts B f T M U) p

/-- The degree-zero alternating differential kills the restriction augmentation.
Source: Stacks Project, Tag 03AN. The two restrictions from the top agree.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverSectionAugmentation_d (f : X ⟶ Y) (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    {m : ℕ} (U : Fin m → X.Opens) :
    finiteCoverSectionAugmentation B f T M U ≫
      finiteCoverSectionDifferential B f T M U 0 = 0 := by
  let F := finiteCoverSectionPresheaf B f T M
  apply biproduct.hom_ext
  intro a
  simp only [finiteCoverSectionDifferential, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp,
    finiteOrderedCechCoface, finiteCoverIntersection, Category.assoc, biproduct.lift_π,
    finiteCoverSectionAugmentation, biproduct.lift_π_assoc,
    CategoryTheory.Limits.zero_comp]
  change (∑ j : Fin 2, (-1 : ℤ) ^ (j : ℕ) •
    (F.map (homOfLE (le_top : (⨅ k, U ((j.succAboveOrderEmb.trans a) k)) ≤ ⊤)).op ≫
      F.map (homOfLE (le_iInf fun k ↦
        iInf_le (fun l ↦ U (a l)) (j.succAbove k))).op)) = 0
  simp only [← F.map_comp, ← op_comp, homOfLE_comp, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul]
  rw [add_neg_eq_zero]

/-- Projection of a test pullback onto its open subscheme.
Source: Stacks Project, Tag 03AN, base change of a covering.
(blueprint: new-finite-cover-row-sections) -/
def finiteCoverTestObjectProjection (f : X ⟶ Y) (T : Y.Etale) (V : X.Opens) :
    finiteCoverTestObject f T V ⟶ Scheme.Etale.mk V.ι :=
  MorphismProperty.Over.homMk (pullback.snd T.hom (V.ι ≫ f)) (by simp [finiteCoverTestObject])

/-- The test pullback square for any inclusion of opens is cartesian.
Source: Stacks Project, Tag 03AN. Cancel the right-hand pullback square from
its composite with the left-hand square.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverTestObjectHom_isPullback (f : X ⟶ Y) (T : Y.Etale)
    {V W : X.Opens} (h : V ≤ W) :
    IsPullback (finiteCoverTestObjectHom f T h) (finiteCoverTestObjectProjection f T V)
      (finiteCoverTestObjectProjection f T W)
      (MorphismProperty.Over.homMk (X.homOfLE h) (by simp)) := by
  apply IsPullback.of_map (Scheme.Etale.forget X ⋙ Over.forget X)
  · apply MorphismProperty.Over.Hom.ext
    change @Eq (pullback T.hom (V.ι ≫ f) ⟶ (W : Scheme)) _ _
    simp [finiteCoverTestObjectHom, finiteCoverTestObjectProjection]
  · let g := (finiteCoverTestObjectHom f T h).left
    have hs : IsPullback (g ≫ pullback.fst T.hom (W.ι ≫ f))
        (pullback.snd T.hom (V.ι ≫ f)) T.hom (X.homOfLE h ≫ (W.ι ≫ f)) := by
      simpa [g, finiteCoverTestObjectHom, Category.assoc] using
        (IsPullback.of_hasPullback T.hom (V.ι ≫ f))
    exact hs.of_right (by
      change g ≫ pullback.snd T.hom (W.ι ≫ f) =
        pullback.snd T.hom (V.ι ≫ f) ≫ X.homOfLE h
      simp only [g, finiteCoverTestObjectHom, MorphismProperty.Over.homMk_hom,
        Over.homMk_left, pullback.map, pullback.lift_snd])
      (IsPullback.of_hasPullback T.hom (W.ι ≫ f))

/-- The inverse images of a finite open cover cover each total test object.
Source: Stacks Project, Tag 03AN. The open inclusions cover the top open;
the preceding cartesian squares identify this family with its base change.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverTestObject_cover (f : X ⟶ Y) (T : Y.Etale) {m : ℕ}
    (U : Fin m → X.Opens) (hU : iSup U = ⊤) :
    Sieve.ofArrows (fun i ↦ finiteCoverTestObject f T (U i))
      (fun i ↦ finiteCoverTestObjectHom f T (le_top : U i ≤ ⊤)) ∈
        X.smallEtaleTopology (finiteCoverTestObject f T ⊤) := by
  let π (i : Fin m) : Scheme.Etale.mk (U i).ι ⟶ Scheme.Etale.mk (⊤ : X.Opens).ι :=
    MorphismProperty.Over.homMk (X.homOfLE le_top) (by simp)
  have hπ : Sieve.ofArrows (fun i ↦ Scheme.Etale.mk (U i).ι) π ∈
      X.smallEtaleTopology (Scheme.Etale.mk (⊤ : X.Opens).ι) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    have hz : z.val ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    refine ⟨i, ⟨z.val, hi⟩, ?_⟩
    change X.homOfLE (le_top : U i ≤ ⊤) ⟨z.val, hi⟩ = z
    apply Subtype.ext
    exact X.homOfLE_apply (le_top : U i ≤ ⊤) ⟨z.val, hi⟩
  rw [Sieve.ofArrows_eq_pullback_of_isPullback π
    (fun i ↦ finiteCoverTestObjectHom_isPullback f T (le_top : U i ≤ ⊤))]
  exact X.smallEtaleTopology.pullback_stable (finiteCoverTestObjectProjection f T ⊤) hπ

/-- Pairwise intersections of the pulled-back opens are the actual fiber products.
Source: Stacks Project, Tags 03AN and 03FC. Paste the cartesian square over the
open intersection with the cartesian test-object square, then cancel the square
for the first open. This makes the geometric overlap used by both row arguments
explicit, without a postponed comparison.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverTestObject_inf_isPullback (f : X ⟶ Y) (T : Y.Etale)
    (V W : X.Opens) :
    IsPullback (finiteCoverTestObjectHom f T (inf_le_left : V ⊓ W ≤ V))
      (finiteCoverTestObjectHom f T (inf_le_right : V ⊓ W ≤ W))
      (finiteCoverTestObjectHom f T (le_top : V ≤ ⊤))
      (finiteCoverTestObjectHom f T (le_top : W ≤ ⊤)) := by
  let e (A A' : X.Opens) (h : A ≤ A') : Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk A'.ι :=
    MorphismProperty.Over.homMk (X.homOfLE h) (by simp)
  have hOpen : IsPullback (e (V ⊓ W) V inf_le_left) (e (V ⊓ W) W inf_le_right)
      (e V ⊤ le_top) (e W ⊤ le_top) := by
    apply IsPullback.of_map (Scheme.Etale.forget X ⋙ Over.forget X)
    · apply MorphismProperty.Over.Hom.ext
      exact (X.homOfLE_homOfLE inf_le_left le_top).trans
        (X.homOfLE_homOfLE inf_le_right le_top).symm
    · exact isPullback_opens_inf_le le_top le_top
  have hV := finiteCoverTestObjectHom_isPullback f T (inf_le_left : V ⊓ W ≤ V)
  have hW := finiteCoverTestObjectHom_isPullback f T (inf_le_right : V ⊓ W ≤ W)
  have hVtop := finiteCoverTestObjectHom_isPullback f T (le_top : V ≤ ⊤)
  have hWtop := finiteCoverTestObjectHom_isPullback f T (le_top : W ≤ ⊤)
  have hOuter := hW.flip.paste_horiz hOpen
  have hOuter' : IsPullback
      (finiteCoverTestObjectHom f T (inf_le_left : V ⊓ W ≤ V) ≫
        finiteCoverTestObjectProjection f T V)
      (finiteCoverTestObjectHom f T (inf_le_right : V ⊓ W ≤ W))
      (e V ⊤ le_top)
      (finiteCoverTestObjectHom f T (le_top : W ≤ ⊤) ≫
        finiteCoverTestObjectProjection f T ⊤) := by
    rw [hV.w, hWtop.w]
    exact hOuter
  apply hOuter'.of_right _ hVtop.flip
  let F := finiteCoverTestObjectFunctor f T
  change F.map (homOfLE (inf_le_left : V ⊓ W ≤ V)) ≫ F.map (homOfLE le_top) =
    F.map (homOfLE (inf_le_right : V ⊓ W ≤ W)) ≫ F.map (homOfLE le_top)
  simp only [← F.map_comp, homOfLE_comp]

/-- Compatible sections on the pulled-back cover have a common section.
Source: Stacks Project, Tag 03AN. The cartesian overlap square converts
pairwise compatibility into compatibility for every pair of arrows. Apply
sheaf amalgamation to the linear maps from the rank-one free module and
evaluate the resulting map at one.
(blueprint: new-finite-cover-row-sections) -/
theorem finiteCoverSection_glue (f : X ⟶ Y) (T : Y.Etale) {m : ℕ}
    (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (s : ∀ i, M.obj.obj (op (finiteCoverTestObject f T (U i))))
    (hs : ∀ i j,
      M.obj.map (finiteCoverTestObjectHom f T (inf_le_left : U i ⊓ U j ≤ U i)).op
          (s i) =
        M.obj.map (finiteCoverTestObjectHom f T (inf_le_right : U i ⊓ U j ≤ U j)).op
          (s j)) :
    ∃ t : M.obj.obj (op (finiteCoverTestObject f T ⊤)),
      ∀ i, M.obj.map (finiteCoverTestObjectHom f T (le_top : U i ≤ ⊤)).op t = s i := by
  let E := ModuleCat.of B B
  let x (i : Fin m) : E ⟶ M.obj.obj (op (finiteCoverTestObject f T (U i))) :=
    ModuleCat.ofHom
      { toFun := fun b ↦ b • s i
        map_add' := by intro b c; exact add_smul b c (s i)
        map_smul' := by intro b c; exact (smul_smul b c (s i)).symm }
  have hx {Z : X.Etale} {i j : Fin m}
      (a : Z ⟶ finiteCoverTestObject f T (U i))
      (b : Z ⟶ finiteCoverTestObject f T (U j))
      (hab : a ≫ finiteCoverTestObjectHom f T (le_top : U i ≤ ⊤) =
        b ≫ finiteCoverTestObjectHom f T (le_top : U j ≤ ⊤)) :
      x i ≫ M.obj.map a.op = x j ≫ M.obj.map b.op := by
    let P := finiteCoverTestObject_inf_isPullback f T (U i) (U j)
    let c := P.lift a b hab
    have hc := congrArg (fun z ↦ M.obj.map c.op z) (hs i j)
    simp only [← ConcreteCategory.comp_apply, ← M.obj.map_comp, ← op_comp] at hc
    dsimp only [c] at hc
    rw [P.lift_fst, P.lift_snd] at hc
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change M.obj.map a.op (r • s i) = M.obj.map b.op (r • s j)
    simpa only [map_smul] using congrArg (fun z ↦ r • z) hc
  obtain ⟨g, hg, _⟩ := M.property.existsUnique_amalgamation_ofArrows
    (fun i ↦ finiteCoverTestObjectHom f T (le_top : U i ≤ ⊤))
    (finiteCoverTestObject_cover f T U hU) x (by
      intro Z i j a b h
      exact hx a b h)
  refine ⟨g 1, ?_⟩
  intro i
  have hi := ConcreteCategory.congr_hom (hg i) (1 : B)
  change M.obj.map (finiteCoverTestObjectHom f T (le_top : U i ≤ ⊤)).op
    (g 1) = (1 : B) • s i at hi
  simpa only [one_smul] using hi

end AlgebraicGeometry.Etale
