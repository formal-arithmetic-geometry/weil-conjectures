/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementConstruction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSitesSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.RingedKFlatWordComparisonDescent
import all WeilConjectures.SixFunctors.OpenOperationModels
import WeilConjectures.AlgebraicGeometry.DivisibleExtensionDerivedReductionSupplement

/-! # Normalized mixed scalar and geometric comparisons

Source: Stacks Project, Modules on Sites and Cohomology on Sites.
(blueprint: lem-pur-ringed-refinement-scalar-comparisons).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

attribute [local irreducible] Coefficients.rings Functor.leftAdjoint

private local instance scalarRestriction_limits {m : Mode} (W : Scheme.{u})
    {A B : Rings m W} (a : A ⟶ B) :
    PreservesFiniteLimits (restrictScalars.{u + 1}
      ((sheafCompose (topology m W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)) := by
  obtain ⟨h, _, _⟩ := sheafRingCoefficientOrdinaryAdjunction a
  exact h

private local instance scalarRestriction_colimits {m : Mode} (W : Scheme.{u})
    {A B : Rings m W} (a : A ⟶ B) :
    PreservesFiniteColimits (restrictScalars.{u + 1}
      ((sheafCompose (topology m W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)) := by
  obtain ⟨_, h, _⟩ := sheafRingCoefficientOrdinaryAdjunction a
  exact h

private theorem scalarAdjunction_exists {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) (W : Over T)
    {A B : Rings m T} (a : A ⟶ B) :
    ∃ adj : (o.scalar W a).E ⊣ restrictScalars.{u + 1}
        ((sheafCompose (topology m W.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings W).map a)),
      ∀ (M : Mod ((c.rings W).obj A)) (Z : (Site m W.left)ᵒᵖ)
        (x : M.val.obj Z),
        (adj.unit.app M).val.app Z x =
          (eqToHom ((o.scalar W a).obj_eq M).symm).val.app Z
            (SuccessiveDerivedQuotient.pure ((c.rings W).map a) M Z 1 x) := by
  obtain ⟨_, _, hadj⟩ := sheafRingCoefficientOrdinaryAdjunction ((c.rings W).map a)
  obtain ⟨adj, hn⟩ := hadj (o.scalar W a).E (o.scalar W a).obj_eq
    (o.scalar W a).map_eq
  refine ⟨adj, ?_⟩
  intro M Z x
  have h := hn M ((o.scalar W a).E.obj M)
    (eqToHom ((o.scalar W a).obj_eq M).symm) Z x
  simpa only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id,
    SuccessiveDerivedQuotient.pure] using h

private theorem structural_naturality {m : Mode} {T : Scheme.{u}}
    (c : Coefficients m T) {U V : Over T} (f : U ⟶ V)
    {A B : Rings m T} (a : A ⟶ B) :
    (c.rings V).map a ≫ c.structural f B =
      c.structural f A ≫
        ((baseChange m f.left).sheafPushforwardContinuous CommRingCat.{u + 1}
          (topology m V.left) (topology m U.left)).map ((c.rings U).map a) := by
  apply (ringAdjunction m f.left).homEquiv_naturality_left_square
  exact (c.pull f).hom.naturality a

private noncomputable def restrictionSquare
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R S : Sheaf J RingCat.{u + 1}} {R' S' : Sheaf K RingCat.{u + 1}}
    (a : R ⟶ S) (b : R' ⟶ S')
    (p : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R')
    (q : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S')
    (h : a ≫ q = p ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map b) :
    restrictScalars.{u + 1} b ⋙ pushforward p ≅ pushforward q ⋙ restrictScalars a :=
  (pushforwardComp (F := F) (G := 𝟭 D) p b) ≪≫
    pushforwardCongr h.symm ≪≫
      (pushforwardComp (F := 𝟭 C) (G := F) a q).symm

private noncomputable def restrictionIso {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) {U V : Over T} (f : U ⟶ V)
    {A B : Rings m T} (a : A ⟶ B) :
    restrictScalars.{u + 1} ((sheafCompose (topology m U.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings U).map a)) ⋙
      (o.operation f A).pushforward ≅
      (o.operation f B).pushforward ⋙ restrictScalars.{u + 1}
        ((sheafCompose (topology m V.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings V).map a)) := by
  let aU := (sheafCompose (topology m U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings U).map a)
  let aV := (sheafCompose (topology m V.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings V).map a)
  have h : aV ≫ (o.operation f B).coefficient = (o.operation f A).coefficient ≫
      ((baseChange m f.left).sheafPushforwardContinuous RingCat.{u + 1}
        (topology m V.left) (topology m U.left)).map aU := by
    rw [o.coefficient f A, o.coefficient f B]
    exact congrArg (fun g ↦ (sheafCompose (topology m V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
        (structural_naturality c f a)
  exact restrictionSquare (baseChange m f.left) aV aU
    (o.operation f A).coefficient (o.operation f B).coefficient h

private theorem restrictionIso_sections {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) {U V : Over T} (f : U ⟶ V)
    {A B : Rings m T} (a : A ⟶ B) (N : Mod ((c.rings U).obj B))
    (Z : (Site m V.left)ᵒᵖ) (x : N.val.obj ((baseChange m f.left).op.obj Z)) :
    HEq (((restrictionIso o f a).hom.app N).val.app Z x) x := by
  rfl

private theorem baseChange_flat (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RepresentablyFlat (baseChange m f) := by
  cases m with
  | ordinary =>
    exact flat_of_preservesFiniteLimits (AlgebraicGeometry.Scheme.proEtaleBaseChange f)
  | systems =>
    have : RepresentablyFlat (AlgebraicGeometry.Scheme.proEtaleBaseChange f) :=
      flat_of_preservesFiniteLimits _
    constructor
    intro W
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence W.1 W.2 (𝟭 ℕ)
        (AlgebraicGeometry.Scheme.proEtaleBaseChange f)).symm

private theorem operation_preserves_kflat {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) {U V : Over T} (f : U ⟶ V)
    (A : Rings m T) (P : CochainComplex (Mod ((c.rings V).obj A)) ℤ)
    (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := topology m V.left)
      (R := (c.rings V).obj A) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((o.operation f A).pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := baseChange m f.left
  have : RepresentablyFlat F := baseChange_flat m f.left
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  let L := Functor.sheafPullbackConstruction.sheafPullback F (Type (u + 1))
    (topology m V.left) (topology m U.left)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type (u + 1))
    (topology m V.left) (topology m U.left)
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  obtain ⟨RI, I, b, E, hE, hobj, hmap, ⟨ae⟩⟩ :=
    RingedPresentationOnSites.continuous_ringed_pullback_presentation
      F L adj ((c.rings U).obj A) ((c.rings V).obj A) (c.structural f A)
  let : E.Additive := hE
  have hc : (o.operation f A).pushforward =
      pushforward ((sheafCompose (topology m V.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (c.structural f A)) := by
    dsimp only [Operation.pushforward]
    rw [o.coefficient f A]
    rfl
  let ae' : E ⊣ (o.operation f A).pushforward := ae.ofNatIsoRight (eqToIso hc).symm
  let e := ae'.leftAdjointUniq (o.operation f A).moduleAdjunction
  have h := (isKFlat_ringedToposPullback L _ adj I b E hobj hmap P hk hf).1
  exact kFlat_iso_independent ((c.rings U).obj A)
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) h

private noncomputable def ordinaryIso {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c)
    (adj : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
      (o.scalar W a).E ⊣ restrictScalars.{u + 1}
        ((sheafCompose (topology m W.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings W).map a)))
    {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B) :
    (o.scalar V a).E ⋙ (o.operation f B).pullback ≅
      (o.operation f A).pullback ⋙ (o.scalar U a).E :=
  ((conjugateIsoEquiv
    ((adj V a).comp (o.operation f B).moduleAdjunction)
    ((o.operation f A).moduleAdjunction.comp (adj U a))).symm
      (restrictionIso o f a).symm).symm

private theorem derivedIso_exists {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) {U V : Over T} (f : U ⟶ V)
    {A B : Rings m T} (a : A ⟶ B)
    (ordinary : (o.scalar V a).E ⋙ (o.operation f B).pullback ≅
      (o.operation f A).pullback ⋙ (o.scalar U a).E) :
    ∃ pull : (o.scalar V a).T ⋙ (o.operation f B).left ≅
        (o.operation f A).left ⋙ (o.scalar U a).T,
      ∀ (P : CochainComplex (Mod ((c.rings V).obj A)) ℤ),
        P.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := topology m V.left)
          (R := (c.rings V).obj A) (P.X n)) →
        pull.hom.app (DerivedCategory.Q.obj P) ≫
            (o.scalar U a).T.map
              ((o.operation f A).pullback.mapDerivedCategoryFactors.hom.app P) ≫
            (o.scalar U a).ε.app
              (((o.operation f A).pullback.mapHomologicalComplex (.up ℤ)).obj P) =
          (o.operation f B).left.map ((o.scalar V a).ε.app P) ≫
            (o.operation f B).pullback.mapDerivedCategoryFactors.hom.app
              (((o.scalar V a).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) := by
  let res := fun P : CochainComplex (Mod ((c.rings V).obj A)) ℤ ↦
    P.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, IsFlatOnSite (J := topology m V.left)
        (R := (c.rings V).obj A) (P.X n)
  have hres : ∀ K, ∃ (P : CochainComplex (Mod ((c.rings V).obj A)) ℤ)
      (p : P ⟶ K), QuasiIso p ∧ res P := by
    intro K
    obtain ⟨P, p, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
    refine ⟨P, p, hq, hk, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso ((c.rings V).obj A) (P.X n)).symm (hf n)
  let F := (o.scalar V a).T ⋙ (o.operation f B).left
  let G := (o.operation f A).left ⋙ (o.scalar U a).T
  let FC := (o.scalar V a).E.mapHomologicalComplex (.up ℤ) ⋙
    (o.operation f B).pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let GC := (o.operation f A).pullback.mapHomologicalComplex (.up ℤ) ⋙
    (o.scalar U a).E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let εF : DerivedCategory.Q ⋙ F ⟶ FC :=
    Functor.whiskerRight (o.scalar V a).ε (o.operation f B).left ≫
      Functor.whiskerLeft ((o.scalar V a).E.mapHomologicalComplex (.up ℤ))
        (o.operation f B).pullback.mapDerivedCategoryFactors.hom
  let εG : DerivedCategory.Q ⋙ G ⟶ GC :=
    Functor.whiskerRight (o.operation f A).pullback.mapDerivedCategoryFactors.hom
        (o.scalar U a).T ≫
      Functor.whiskerLeft ((o.operation f A).pullback.mapHomologicalComplex (.up ℤ))
        (o.scalar U a).ε
  let t : FC ≅ GC := Functor.isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)) DerivedCategory.Q
  have hF : ∀ P, res P → IsIso (εF.app P) := by
    intro P hP
    have := (o.scalar V a).computes P hP.1
    change IsIso ((o.operation f B).left.map ((o.scalar V a).ε.app P) ≫
      (o.operation f B).pullback.mapDerivedCategoryFactors.hom.app _)
    exact IsIso.comp_isIso' (Functor.map_isIso _ _)
      (((o.operation f B).pullback.mapDerivedCategoryFactors.app _).isIso_hom)
  have hG : ∀ P, res P → IsIso (εG.app P) := by
    intro P hP
    have := (o.scalar U a).computes
      (((o.operation f A).pullback.mapHomologicalComplex (.up ℤ)).obj P)
      (operation_preserves_kflat o f A P hP.1 hP.2)
    change IsIso ((o.scalar U a).T.map
      ((o.operation f A).pullback.mapDerivedCategoryFactors.hom.app P) ≫
        (o.scalar U a).ε.app _)
    infer_instance
  obtain ⟨e, he, _⟩ := CategoryTheory.RingedKFlatWord.comparison_descent_iso
    res hres F G FC GC εF εG hF hG t
  refine ⟨e, ?_⟩
  intro P hk hf
  have h := he P ⟨hk, hf⟩
  have ht : t.hom.app P = DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) := by
    rfl
  rw [ht] at h
  change e.hom.app (DerivedCategory.Q.obj P) ≫
      ((o.scalar U a).T.map
        ((o.operation f A).pullback.mapDerivedCategoryFactors.hom.app P) ≫
          (o.scalar U a).ε.app _) =
    ((o.operation f B).left.map ((o.scalar V a).ε.app P) ≫
      (o.operation f B).pullback.mapDerivedCategoryFactors.hom.app _) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) at h
  exact h.trans (Category.assoc _ _ _)

private noncomputable def openRingIso {m : Mode} {T : Scheme.{u}}
    (c : Coefficients m T) {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left] :
    c.rings U ≅ c.rings V ⋙
      (openInclusion m j.left).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology m U.left) (topology m V.left) :=
  (c.pull j).symm ≪≫ Functor.isoWhiskerLeft (c.rings V)
    (Adjunction.leftAdjointUniq
      ((openSiteAdjunction m j.left).sheafPushforwardContinuous
        (E := CommRingCat.{u + 1}) (topology m U.left) (topology m V.left))
      (ringAdjunction m j.left)).symm

private theorem openRingIso_unit {m : Mode} {T : Scheme.{u}}
    (c : Coefficients m T) {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (A : Rings m T) :
    (((openSiteAdjunction m j.left).sheafPushforwardContinuous
      (E := CommRingCat.{u + 1}) (topology m U.left) (topology m V.left)).unit.app
        ((c.rings V).obj A)) ≫
      ((baseChange m j.left).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology m V.left) (topology m U.left)).map ((openRingIso c j).inv.app A) =
        c.structural j A := by
  let adj := (openSiteAdjunction m j.left).sheafPushforwardContinuous
    (E := CommRingCat.{u + 1}) (topology m U.left) (topology m V.left)
  change adj.homEquiv _ _ ((openRingIso c j).inv.app A) = _
  change adj.homEquiv _ _
    ((adj.leftAdjointUniq (ringAdjunction m j.left)).hom.app ((c.rings V).obj A) ≫
      (c.pull j).hom.app A) = _
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

private noncomputable def ringIsoPushforwardAdj
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) {R : Sheaf K RingCat.{u + 1}} {S : Sheaf J RingCat.{u + 1}}
    (e : S ≅ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R) :
    pushforward.{u + 1} e.hom ⊣ pushforward.{u + 1}
      ((a.sheafPushforwardContinuous J K).unit.app R ≫
        (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map e.inv) := by
  let shAdj := a.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K
  let ψ := shAdj.unit.app R ≫
    (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map e.inv
  refine pushforwardPushforwardAdj a e.hom ψ ?_ ?_
  · have h : shAdj.unit.app R = ψ ≫
        (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map e.hom := by
      dsimp only [ψ]
      rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
      rw [(G.sheafPushforwardContinuous RingCat.{u + 1} K J).map_id]
      exact (Category.comp_id _).symm
    exact congrArg (fun t ↦ t.hom) h
  · change (e.hom ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ψ ≫
      shAdj.counit.app S).hom = (𝟙 S : S ⟶ S).hom
    have ht : (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ψ ≫
        shAdj.counit.app S = e.inv := (shAdj.homEquiv R S).symm_apply_apply e.inv
    rw [ht, Iso.hom_inv_id]

private noncomputable def openRestrictionPresentation {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) {U V : Over T} (j : U ⟶ V)
    [IsOpenImmersion j.left] (A : Rings m T) :
    pushforward.{u + 1} (F := openInclusion m j.left)
      ((sheafCompose (topology m U.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((openRingIso c j).hom.app A)) ≅ (o.operation j A).pullback := by
  let a := openSiteAdjunction m j.left
  let shAdj := a.sheafPushforwardContinuous
    (E := RingCat.{u + 1}) (topology m U.left) (topology m V.left)
  let eφ : (sheafCompose (topology m U.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((c.rings U).obj A) ≅
      ((openInclusion m j.left).sheafPushforwardContinuous RingCat.{u + 1}
        (topology m U.left) (topology m V.left)).obj
          ((sheafCompose (topology m V.left)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((c.rings V).obj A)) :=
    (sheafCompose (topology m U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso ((openRingIso c j).app A)
  let φ := eφ.hom
  let ψ := shAdj.unit.app ((sheafCompose (topology m V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((c.rings V).obj A)) ≫
    ((baseChange m j.left).sheafPushforwardContinuous RingCat.{u + 1}
      (topology m V.left) (topology m U.left)).map eφ.inv
  have hψ' : ψ = (sheafCompose (topology m V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (openRightCoefficient m j.left ((c.rings V).obj A) ≫
          ((baseChange m j.left).sheafPushforwardContinuous CommRingCat.{u + 1}
            (topology m V.left) (topology m U.left)).map
              ((openRingIso c j).inv.app A)) := by
    dsimp only [ψ]
    rfl
  have hψ : ψ = (o.operation j A).coefficient := by
    rw [hψ', o.coefficient j A]
    exact congrArg ((sheafCompose (topology m V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (openRingIso_unit c j A)
  let adj : pushforward.{u + 1} (F := openInclusion m j.left) φ ⊣
      pushforward.{u + 1} (F := baseChange m j.left) ψ :=
    ringIsoPushforwardAdj a
      (R := (sheafCompose (topology m V.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((c.rings V).obj A)) eφ
  exact (adj.ofNatIsoRight (pushforwardCongr hψ)).leftAdjointUniq
    (o.operation j A).moduleAdjunction

private noncomputable def openRestrictionScalarIso {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) {U V : Over T} (j : U ⟶ V)
    [IsOpenImmersion j.left] {A B : Rings m T} (a : A ⟶ B) :
    restrictScalars.{u + 1} ((sheafCompose (topology m V.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings V).map a)) ⋙
      (o.operation j A).pullback ≅
      (o.operation j B).pullback ⋙ restrictScalars.{u + 1}
        ((sheafCompose (topology m U.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings U).map a)) := by
  let φA := (sheafCompose (topology m U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((openRingIso c j).hom.app A)
  let φB := (sheafCompose (topology m U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((openRingIso c j).hom.app B)
  let aU := (sheafCompose (topology m U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings U).map a)
  let aV := (sheafCompose (topology m V.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings V).map a)
  have h : aU ≫ φB = φA ≫
      ((openInclusion m j.left).sheafPushforwardContinuous RingCat.{u + 1}
        (topology m U.left) (topology m V.left)).map aV := by
    exact congrArg (fun g ↦ (sheafCompose (topology m U.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
        ((openRingIso c j).hom.naturality a)
  exact Functor.isoWhiskerLeft (restrictScalars aV)
      (openRestrictionPresentation o j A).symm ≪≫
    restrictionSquare (openInclusion m j.left) aU aV φA φB h ≪≫
    Functor.isoWhiskerRight (openRestrictionPresentation o j B) (restrictScalars aU)

private theorem openUnit_isIso {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    (A : Rings m T) (M : category c U A) :
    IsIso ((o.openAdjunction j A).unit.app M) := by
  let a := o.openAdjunction j A
  have hQ (P : CochainComplex (Mod ((c.rings U).obj A)) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso (((o.openModel j A).adjunction.mapHomologicalComplex
        (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ, IsIso
          ((((o.openModel j A).adjunction.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ (o.openModel j A).unit (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map
          (((o.openModel j A).adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        (o.operation j A).pullback.mapDerivedCategoryFactors.inv.app _ ≫
        (o.operation j A).left.map
          ((o.openModel j A).functor.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, Calculus.openAdjunction, exactDerivedAdjunction,
        Adjunction.localization_unit_app]
      rfl
    rw [hu]
    refine IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' ?_ ?_)
    · exact ((o.operation j A).pullback.mapDerivedCategoryFactors.app _).isIso_inv
    · exact Functor.map_isIso _ _
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

private theorem scalar_open_supported {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) {U V : Over T} (j : U ⟶ V)
    [IsOpenImmersion j.left] {A B : Rings m T} (a : A ⟶ B) (M : category c U A) :
    (o.shriek j B).essImage ((o.scalar V a).T.obj ((o.shriek j A).obj M)) := by
  let rV := restrictScalars.{u + 1} ((sheafCompose (topology m V.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings V).map a))
  let rU := restrictScalars.{u + 1} ((sheafCompose (topology m U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings U).map a))
  let adjV := sheafScalarDerivedAdjunction ((c.rings V).map a) (o.scalar V a)
  let adjU := sheafScalarDerivedAdjunction ((c.rings U).map a) (o.scalar U a)
  let e : rV.mapDerivedCategory ⋙ (o.operation j A).left ≅
      (o.operation j B).left ⋙ rU.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso rV (o.operation j A).pullback).symm ≪≫
      Functor.mapDerivedCategoryNatIso (openRestrictionScalarIso o j a) ≪≫
      Functor.mapDerivedCategoryCompIso (o.operation j B).pullback rU
  let k := ((o.openAdjunction j A).comp adjV).ofNatIsoRight e
  let l := adjU.comp (o.openAdjunction j B)
  let d := k.leftAdjointUniq l
  exact ⟨(o.scalar U a).T.obj M, ⟨(d.app M).symm⟩⟩

private theorem delta_exists {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
    {A B : Rings m T} (a : A ⟶ B)
    (pull : (o.scalar V a).T ⋙ (o.operation j B).left ≅
      (o.operation j A).left ⋙ (o.scalar U a).T) :
    ∃ delta : o.shriek j A ⋙ (o.scalar V a).T ≅ (o.scalar U a).T ⋙ o.shriek j B,
      ∀ M : category c U A,
        (o.openAdjunction j B).homEquiv _ _ (delta.inv.app M) =
          (o.scalar U a).T.map ((o.openAdjunction j A).unit.app M) ≫
            pull.inv.app ((o.shriek j A).obj M) := by
  let β := ((mateEquiv (o.openAdjunction j A) (o.openAdjunction j B)).symm
    (TwoSquare.mk _ _ _ _ pull.inv)).natTrans
  have hu : ∀ M, IsIso ((o.openAdjunction j B).unit.app M) := openUnit_isIso o j B
  have : IsIso (o.openAdjunction j B).unit := NatIso.isIso_of_isIso_app _
  have hβ (M : category c U A) : IsIso (β.app M) := by
    have htrans : (o.openAdjunction j B).homEquiv _ _ (β.app M) =
        (o.scalar U a).T.map ((o.openAdjunction j A).unit.app M) ≫
          pull.inv.app ((o.shriek j A).obj M) := by
      exact (unit_mateEquiv_symm (o.openAdjunction j A) (o.openAdjunction j B)
        (TwoSquare.mk _ _ _ _ pull.inv) M).symm
    have : IsIso ((o.openAdjunction j A).unit.app M) := openUnit_isIso o j A M
    have : IsIso ((o.openAdjunction j B).homEquiv _ _ (β.app M)) := by
      rw [htrans]
      infer_instance
    have : (o.shriek j B).Full := (o.openAdjunction j B).fullyFaithfulLOfIsIsoUnit.full
    have : (o.shriek j B).Faithful :=
      (o.openAdjunction j B).fullyFaithfulLOfIsIsoUnit.faithful
    have : IsIso ((o.openAdjunction j B).counit.app
        ((o.scalar V a).T.obj ((o.shriek j A).obj M))) :=
      (o.openAdjunction j B).isIso_counit_app_iff_mem_essImage.mpr
        (scalar_open_supported o j a M)
    have he : β.app M = (o.shriek j B).map
        ((o.openAdjunction j B).homEquiv _ _ (β.app M)) ≫
          (o.openAdjunction j B).counit.app _ :=
      ((o.openAdjunction j B).homEquiv _ _).symm_apply_apply (β.app M) |>.symm
    rw [he]
    change IsIso ((o.shriek j B).map
      ((o.openAdjunction j B).homEquiv _ _ (β.app M)) ≫
        (o.openAdjunction j B).counit.app
          ((o.scalar V a).T.obj ((o.shriek j A).obj M)))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app _
  refine ⟨(asIso β).symm, ?_⟩
  intro M
  exact (unit_mateEquiv_symm (o.openAdjunction j A) (o.openAdjunction j B)
    (TwoSquare.mk _ _ _ _ pull.inv) M).symm

/-- Scalar extension commutes with geometric pullback and open extension, with the
normalizations prescribed by the refinement calculus.

Source: Stacks Project, Modules on Sites, Tags 03EL, 03DI and 03DJ; Cohomology on
Sites, Tags 06YY, 07A6, 0D6D and 0G7E; Steps 6--7 of
`lem-route-ringed-refinement-core`.
(blueprint: lem-pur-ringed-refinement-scalar-comparisons).

Proof: identify each recorded ordinary scalar functor with sheafified extension
of scalars using its object and map equations. Transport the tensor/restriction
adjunction along this isomorphism. Its unit sends x to the sheafified tensor 1⊗x,
which gives `ordinaryAdjunction` and `insertion`.

For an arrow f and ambient coefficient map a, naturality of the ring inverse-image
compositor gives the square relating `c.structural f A`, `c.structural f B` and the
two inverse images of a. Define the restriction/direct-image isomorphism by the
identity on sections. The ring square proves linearity; naturality and the inverse
identities are sectionwise identities. Transport it through `o.coefficient` to
the actual pushforwards of o. Define the ordinary scalar/pullback isomorphism as
the inverse conjugate of this restriction isomorphism under the composed ordinary
adjunctions. The inverse laws for the conjugate equivalence prove `ordinary_mate`.

Present the geometric inverse image by its tensor-formula model, using the
representably flat base-change site functor in both modes. Identify its left adjoint
with the recorded pullback. The ringed-topos K-flat pullback theorem therefore
shows that this pullback preserves K-flatness on flat-term K-flat complexes.
Compose the actual scalar computation arrows with the exact-functor factorization
arrows. Both composites are invertible on this resolving class. Comparison descent
applied to the termwise ordinary isomorphism gives the derived isomorphism with
exactly the required representative equation.

For an open immersion, literal restriction of ring sheaves and ringInverse have
the same right adjoint. Their unique adjunction comparison and c.pull give the
natural ring identification with the open ring. Its unit equation identifies the
structural map, so the explicit pushforward/pushforward adjunction identifies
literal restriction of modules, transported along this ring isomorphism, with the
recorded module pullback. Naturality gives commutation of restriction of scalars
with this pullback. Exact localization and the scalar derived adjunctions show
that scalar extension of an object extended from the open is again in the
essential image of the target open extension.

The exact localized open units are invertible because their termwise components
are invertible. Transpose scalar extension of the source open unit followed by
the inverse pull comparison. Its transpose is invertible, and its target is
supported on the open by the preceding essential-image argument. Thus the target
open counit is invertible, and the adjunction identity makes the original map
invertible. Its inverse defines delta. The inverse law of the Hom equivalence is
precisely delta_inverse. These constructions use the actual ordinary and derived
adjunctions in both modes and impose no flatness on the coefficient map. -/
theorem scalarComparisons_exists (m : Mode) (T : Scheme.{u})
    (o : Calculus (canonicalCoefficients m T)) : Nonempty (ScalarComparisons o) := by
  classical
  let adj := fun (W : Over T) {A B : Rings m T} (a : A ⟶ B) ↦
    (scalarAdjunction_exists o W a).choose
  let ord := fun {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B) ↦
    ordinaryIso o adj f a
  let pull := fun {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B) ↦
    (derivedIso_exists o f a (ord f a)).choose
  let delta := fun {U V : Over T} (j : U ⟶ V) [IsOpenImmersion j.left]
      {A B : Rings m T} (a : A ⟶ B) ↦ (delta_exists o j a (pull j a)).choose
  refine ⟨{
    ordinaryAdjunction := adj
    insertion := fun W {A B} a ↦ (scalarAdjunction_exists o W a).choose_spec
    ordinary := ord
    restriction := restrictionIso o
    restriction_sections := restrictionIso_sections o
    ordinary_mate := ?_
    pull := pull
    representative := fun {U V} f {A B} a ↦ (derivedIso_exists o f a (ord f a)).choose_spec
    delta := delta
    delta_inverse := fun {U V} j [_] {A B} a ↦ (delta_exists o j a (pull j a)).choose_spec }⟩
  intro U V f A B a
  exact (conjugateIsoEquiv
    ((adj V a).comp (o.operation f B).moduleAdjunction)
    ((o.operation f A).moduleAdjunction.comp (adj U a))).apply_symm_apply _

end SheafOfModules.RingedRefinement
