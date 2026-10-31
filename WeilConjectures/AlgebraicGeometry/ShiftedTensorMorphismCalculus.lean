/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Products.Associator
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorComparisonOfUniverses
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
import all WeilConjectures.Algebra.Homology.TotalTensorSignedCoherence
import WeilConjectures.AlgebraicGeometry.CochainPullbackTensorShift
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement

/-!
# Signed calculus of shifted derived tensor morphisms

Source: literature/stacks-project/sites-cohomology.tex, Tags 0FPL and 0FPM
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
-/

@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Keep the tensor and localization APIs folded during elaboration.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
universe u v w

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

universe u₁ v₁ u₂ v₂ w₁ w₂

private theorem descendTensorSwap
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (c : t ≅ CategoryTheory.Prod.swap _ _ ⋙ t)
    (hex : ∀ (U V : D × D ⥤ D)
      (e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ U ≅
        ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F : P.FullSubcategory,
        s.app (q.obj E.obj, q.obj F.obj) = e.app (E, F))
    (hext : ∀ {U V : D × D ⥤ D} (s s' : U ≅ V),
      (∀ E F : P.FullSubcategory, s.app (q.obj E.obj, q.obj F.obj) =
        s'.app (q.obj E.obj, q.obj F.obj)) → s = s') :
    ∃! σ : T ≅ CategoryTheory.Prod.swap _ _ ⋙ T,
      ∀ (X Y : A) (hx : P X) (hy : P Y),
        r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩) ≫ σ.hom.app (q.obj X, q.obj Y) =
          q.map (c.hom.app (X, Y)) ≫ r.hom.app (⟨Y, hy⟩, ⟨X, hx⟩) := by
  let e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ (CategoryTheory.Prod.swap _ _ ⋙ T) :=
    r.symm ≪≫
    isoWhiskerRight (isoWhiskerLeft (P.ι.prod P.ι) c) q ≪≫
    isoWhiskerLeft (CategoryTheory.Prod.swap P.FullSubcategory P.FullSubcategory) r
  obtain ⟨σ, hσ⟩ := hex _ _ e
  have hs (X Y : A) (hx : P X) (hy : P Y) :
      r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩) ≫ σ.hom.app (q.obj X, q.obj Y) =
        q.map (c.hom.app (X, Y)) ≫ r.hom.app (⟨Y, hy⟩, ⟨X, hx⟩) := by
    have ha := congrArg Iso.hom (hσ ⟨X, hx⟩ ⟨Y, hy⟩)
    change σ.hom.app (q.obj X, q.obj Y) = _ at ha
    rw [ha]
    simp only [Iso.app_hom, e, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, NatTrans.comp_app,
      Iso.hom_inv_id_app_assoc]
    rfl
  refine ⟨σ, hs, ?_⟩
  intro σ' hσ'
  apply hext
  rintro ⟨X, hx⟩ ⟨Y, hy⟩
  apply Iso.ext
  exact (cancel_epi (r.hom.app (⟨X, hx⟩, ⟨Y, hy⟩))).1
    ((hσ' X Y hx hy).trans (hs X Y hx hy).symm)

set_option backward.isDefEq.respectTransparency true in
private theorem totalSwapNaturality
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (χ : ∀ E F : CochainComplex A ℤ,
      CochainComplex.mapBifunctor E F (curriedTensor A) ≅
        CochainComplex.mapBifunctor F E (curriedTensor A))
    (hχ : ∀ (E F : CochainComplex A ℤ) (p q : ℤ),
      CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
          (χ E F).hom.f (p + q) =
        ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
          CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p)))
    {E E' F F' : CochainComplex A ℤ} (f : E ⟶ E') (g : F ⟶ F') :
    HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) ≫ (χ E' F').hom =
      (χ E F).hom ≫ HomologicalComplex.mapBifunctorMap g f (curriedTensor A) (.up ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  subst n
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  erw [hχ E' F' p q]
  conv_rhs => erw [← Category.assoc, hχ E F p q]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor]
  rw [← tensorHom_def_assoc, BraidedCategory.braiding_naturality_assoc]
  rw [tensorHom_def, Category.assoc]

@[irreducible]
private def totalSwapNatIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (χ : ∀ E F : CochainComplex A ℤ,
      CochainComplex.mapBifunctor E F (curriedTensor A) ≅
        CochainComplex.mapBifunctor F E (curriedTensor A))
    (hχ : ∀ (E F : CochainComplex A ℤ) (p q : ℤ),
      CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
          (χ E F).hom.f (p + q) =
        ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
          CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p))) :
    Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ≅
      CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj
        ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) := by
  let t := Functor.uncurry.obj
    ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  have hm {E E' F F' : CochainComplex A ℤ} (f : E ⟶ E') (g : F ⟶ F') :
      t.map (Prod.mkHom f g) =
        HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) := by
    simp [t, Functor.map₂HomologicalComplex, Functor.uncurry_obj_map,
      HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  refine NatIso.ofComponents (F := t) (G := CategoryTheory.Prod.swap _ _ ⋙ t)
    (fun X ↦ χ X.1 X.2) ?_
  intro X Y f
  change t.map (X := (X.1, X.2)) (Y := (Y.1, Y.2)) (Prod.mkHom f.1 f.2) ≫
      (χ Y.1 Y.2).hom =
    (χ X.1 X.2).hom ≫
      t.map (X := (X.2, X.1)) (Y := (Y.2, Y.1)) (Prod.mkHom f.2 f.1)
  rw [hm f.1 f.2, hm f.2 f.1]
  exact totalSwapNaturality χ hχ f.1 f.2

private theorem totalSwapNatIso_hom_app
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (χ : ∀ E F : CochainComplex A ℤ,
      CochainComplex.mapBifunctor E F (curriedTensor A) ≅
        CochainComplex.mapBifunctor F E (curriedTensor A))
    (hχ : ∀ (E F : CochainComplex A ℤ) (p q : ℤ),
      CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
          (χ E F).hom.f (p + q) =
        ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
          CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p)))
    (E F : CochainComplex A ℤ) :
    (totalSwapNatIso χ hχ).hom.app (E, F) = (χ E F).hom := by
  unfold totalSwapNatIso
  rfl

@[irreducible]
private def totalComplexSwap
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (E F : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor E F (curriedTensor A) ≅
      CochainComplex.mapBifunctor F E (curriedTensor A) :=
  HomologicalComplex₂.total.mapIso (CochainComplex.Monoidal.braidingBicomplexIso E F)
    (.up ℤ) ≪≫ HomologicalComplex.mapBifunctorFlipIso F E (curriedTensor A) (.up ℤ)

private theorem totalComplexSwap_signed
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [∀ E F : CochainComplex A ℤ,
      CochainComplex.HasMapBifunctor E F (curriedTensor A)]
    (E F : CochainComplex A ℤ) (p q : ℤ) :
    CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
        (totalComplexSwap E F).hom.f (p + q) =
      ((-1 : ℤ) ^ (p * q).natAbs) • ((β_ (E.X p) (F.X q)).hom ≫
        CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q) (add_comm q p)) := by
  have h₁ : CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
      (HomologicalComplex₂.total.map
        (CochainComplex.Monoidal.braidingBicomplexIso E F).hom (.up ℤ)).f (p + q) =
      (β_ (E.X p) (F.X q)).hom ≫
        CochainComplex.ιMapBifunctor E F (curriedTensor A).flip p q (p + q) rfl := by
    erw [HomologicalComplex₂.ιTotal_map]
    rfl
  simp only [totalComplexSwap, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_hom]
  erw [← Category.assoc, h₁]
  erw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom, Units.smul_def,
    Preadditive.comp_zsmul]
  change ((q * p).negOnePow : ℤ) • _ = _
  rw [mul_comm q p]
  have hsign : ((p * q).negOnePow : ℤ) = (-1 : ℤ) ^ (p * q).natAbs :=
    Int.coe_negOnePow ℤ (p * q)
  erw [hsign]

private theorem exactDerivedComparison
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : CochainComplex A ℤ) :
    derivedPullbackComplexComparison F F.mapDerivedCategory F.mapDerivedCategoryFactorsh.hom E =
      F.mapDerivedCategoryFactors.hom.app E := by
  simp only [derivedPullbackComplexComparison,
    Functor.mapDerivedCategoryFactorsh_hom_app, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id _

section BinaryNormalization
variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
  {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
  (q : A ⥤ D) [q.CommShift ℤ] (P : ObjectProperty A)
  (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)

/-- The normalization square for the two-variable shift.
Source: Stacks 0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def TensorShiftNormalization (a b : ℤ)
    (c : ((shiftFunctor A a).prod (shiftFunctor A b)) ⋙ t ≅
      t ⋙ shiftFunctor A (a + b))
    (s : ((shiftFunctor D a).prod (shiftFunctor D b)) ⋙ T ≅
      T ⋙ shiftFunctor D (a + b)) : Prop :=
  ∀ (E F : A) (hE : P E) (hF : P F),
    ∃ (hEa : P (E⟦a⟧)) (hFb : P (F⟦b⟧)),
      r.hom.app (⟨E⟦a⟧, hEa⟩, ⟨F⟦b⟧, hFb⟩) ≫
        T.map (Prod.mkHom ((q.commShiftIso a).hom.app E)
          ((q.commShiftIso b).hom.app F)) ≫ s.hom.app (q.obj E, q.obj F) =
      q.map (c.hom.app (E, F)) ≫ (q.commShiftIso (a + b)).hom.app _ ≫
        (shiftFunctor D (a + b)).map (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩))

end BinaryNormalization

set_option backward.isDefEq.respectTransparency false
section GenericShiftDescent
variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
  {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
  (q : A ⥤ D) [q.CommShift ℤ] (P : ObjectProperty A)
  (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
  (hshift : ∀ (E : P.FullSubcategory) (n : ℤ), P (E.obj⟦n⟧))
  (hex : ∀ (U V : D × D ⥤ D)
    (e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ U ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ V),
    ∃ s : U ≅ V, ∀ E F : P.FullSubcategory,
      s.app (q.obj E.obj, q.obj F.obj) = e.app (E, F))
  (hext : ∀ {U V : D × D ⥤ D} (s s' : U ≅ V),
    (∀ E F : P.FullSubcategory, s.app (q.obj E.obj, q.obj F.obj) =
      s'.app (q.obj E.obj, q.obj F.obj)) → s = s')
include hshift hex hext in
private theorem descendTensorShiftAPI (a b : ℤ)
    (c : ((shiftFunctor A a).prod (shiftFunctor A b)) ⋙ t ≅
      t ⋙ shiftFunctor A (a + b)) :
    ∃! s : ((shiftFunctor D a).prod (shiftFunctor D b)) ⋙ T ≅
        T ⋙ shiftFunctor D (a + b),
      TensorShiftNormalization q P t T r a b c s := by
  let S (n : ℤ) : P.FullSubcategory ⥤ P.FullSubcategory := P.lift
    (P.ι ⋙ shiftFunctor _ n) (fun E ↦
      hshift E n)
  let e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ ((shiftFunctor _ a).prod (shiftFunctor _ b)) ⋙ T ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T ⋙ shiftFunctor _ (a + b) :=
    SheafOfModules.DerivedTensorConstraints.genericShiftConjugate P.ι
    ((P.ι.prod P.ι) ⋙ t) q T S
    (fun n ↦ isoWhiskerLeft P.ι (q.commShiftIso n))
    r a b (isoWhiskerLeft (P.ι.prod P.ι) c)
  obtain ⟨s, hs⟩ := hex _ _ e
  have he (E F : A)
      (hE : P E) (hF : P F) :
      r.hom.app ((S a).obj ⟨E,hE⟩,(S b).obj ⟨F,hF⟩) ≫
        T.map (Prod.mkHom ((q.commShiftIso a).hom.app E)
          ((q.commShiftIso b).hom.app F)) ≫
        s.hom.app (q.obj E,q.obj F) =
      q.map (c.app (E, F)).hom ≫
        (q.commShiftIso (a + b)).hom.app _ ≫
        (shiftFunctor _ (a + b)).map (r.hom.app (⟨E,hE⟩,⟨F,hF⟩)) := by
    have h := congrArg Iso.hom (hs ⟨E,hE⟩ ⟨F,hF⟩)
    change s.hom.app (q.obj E,q.obj F) =
      e.hom.app (⟨E,hE⟩,⟨F,hF⟩) at h
    rw [h]
    dsimp only [e]
    erw [SheafOfModules.DerivedTensorConstraints.genericShiftConjugate_hom_app]
    simp only [isoWhiskerLeft_inv, whiskerLeft_app]
    erw [← T.map_comp_assoc]
    have hi : Prod.mkHom ((q.commShiftIso a).hom.app E)
        ((q.commShiftIso b).hom.app F) ≫
        Prod.mkHom ((q.commShiftIso a).inv.app E)
          ((q.commShiftIso b).inv.app F) = 𝟙 _ :=
      (Iso.prod ((q.commShiftIso a).app E)
        ((q.commShiftIso b).app F)).hom_inv_id
    erw [hi]
    erw [T.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    rfl
  refine ⟨s, (fun E F hE hF ↦ ⟨_,_,he E F hE hF⟩), ?_⟩
  intro s' hs'
  apply hext
  rintro ⟨E,hE⟩ ⟨F,hF⟩
  apply Iso.ext
  obtain ⟨hEa,hFb,h⟩ := hs' E F hE hF
  have hi : IsIso (Prod.mkHom ((q.commShiftIso a).hom.app E)
      ((q.commShiftIso b).hom.app F)) :=
    (Iso.prod ((q.commShiftIso a).app E)
      ((q.commShiftIso b).app F)).isIso_hom
  apply (cancel_epi (T.map (Prod.mkHom
    ((q.commShiftIso a).hom.app E)
    ((q.commShiftIso b).hom.app F)))).1
  apply (cancel_epi (r.hom.app (⟨E⟦a⟧,hEa⟩,⟨F⟦b⟧,hFb⟩))).1
  exact h.trans (he E F hE hF).symm


end GenericShiftDescent
set_option backward.isDefEq.respectTransparency true

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]

/-- Extract the shift in the second input by its functorial shift comparison. -/
def tensorRightShift (b : ℤ) :
    ((𝟭 A).prod (shiftFunctor B b)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z b := by
  refine NatIso.ofComponents (fun E ↦ ((T.obj E.1).commShiftIso b).app E.2) ?_
  intro E F f
  dsimp [Functor.uncurry, CategoryTheory.Functor.prod, Functor.comp]
  rw [Category.assoc]
  erw [((T.obj F.1).commShiftIso b).hom.naturality]
  rw [← Category.assoc, ← NatTrans.shift_app_comm]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

/-- Extract the shift in the first input by its functorial shift comparison. -/
def tensorLeftShift (a : ℤ) :
    ((shiftFunctor A a).prod (𝟭 B)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z a := by
  refine NatIso.ofComponents (fun E ↦ ((T.flip.obj E.2).commShiftIso a).app E.1) ?_
  intro E F f
  dsimp [Functor.uncurry, CategoryTheory.Functor.prod, Functor.comp]
  rw [Category.assoc]
  erw [← NatTrans.shift_app_comm (T.flip.map f.2) a F.1]
  rw [← Category.assoc]
  erw [((T.flip.obj E.2).commShiftIso a).hom.naturality]
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl
end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
  (T : A ⥤ B ⥤ Z) [∀ X, (T.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.map f) ℤ]
  [∀ X, (T.flip.obj X).CommShift ℤ]
  [∀ X Y (f : X ⟶ Y), NatTrans.CommShift (T.flip.map f) ℤ]

/-- Extract two shifts, moving the second shift before the first. -/
def tensorPairShift (a b : ℤ) :
    ((shiftFunctor A a).prod (shiftFunctor B b)) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor Z (a + b) :=
  isoWhiskerLeft ((shiftFunctor A a).prod (𝟭 B)) (tensorRightShift T b) ≪≫
    isoWhiskerRight (tensorLeftShift T a) (shiftFunctor Z b) ≪≫
    isoWhiskerLeft (Functor.uncurry.obj T) (shiftFunctorAdd Z a b).symm

end

section
variable {A B Z : Type*} [Category* A] [Category* B] [Category* Z]
  [Preadditive A] [Preadditive B] [Preadditive Z]
  (F : A ⥤ B ⥤ Z) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ E : CochainComplex A ℤ, ∀ G : CochainComplex B ℤ,
    CochainComplex.HasMapBifunctor E G F]

@[irreducible]
def totalTensorPairShift (a b : ℤ) :
    ((shiftFunctor (CochainComplex A ℤ) a).prod
      (shiftFunctor (CochainComplex B ℤ) b)) ⋙ Functor.uncurry.obj F.map₂CochainComplex ≅
    Functor.uncurry.obj F.map₂CochainComplex ⋙ shiftFunctor _ (a + b) :=
  tensorPairShift F.map₂CochainComplex a b

end



section PullbackPredicates
variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
  {E : Type u₂} [Category.{v₂} E] [HasShift E ℤ]
  (T : D × D ⥤ D) (TS : E × E ⥤ E) (U : D ⥤ E) [U.CommShift ℤ]
  (tR : ∀ a b : ℤ, ((shiftFunctor D a).prod (shiftFunctor D b)) ⋙ T ≅
    T ⋙ shiftFunctor D (a + b))
  (tS : ∀ a b : ℤ, ((shiftFunctor E a).prod (shiftFunctor E b)) ⋙ TS ≅
    TS ⋙ shiftFunctor E (a + b))

/-- The associator, symmetry and shift equations for a tensor comparison.
Source: Stacks 03EL, 07A4 and 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def GenericTensorPullbackCoherence
    (αR : (T.prod (𝟭 D)) ⋙ T ≅
      CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T)
    (σR : T ≅ CategoryTheory.Prod.swap D D ⋙ T)
    (αS : (TS.prod (𝟭 E)) ⋙ TS ≅
      CategoryTheory.prod.associator E E E ⋙ ((𝟭 E).prod TS) ⋙ TS)
    (σS : TS ≅ CategoryTheory.Prod.swap E E ⋙ TS)
    (μ : T ⋙ U ≅ (U.prod U) ⋙ TS) : Prop :=
  (∀ X Y Z : D,
    U.map (αR.hom.app ((X,Y),Z)) ≫ μ.hom.app (X,T.obj (Y,Z)) ≫
      TS.map (Prod.mkHom (𝟙 (U.obj X)) (μ.hom.app (Y,Z))) =
    μ.hom.app (T.obj (X,Y),Z) ≫
      TS.map (Prod.mkHom (μ.hom.app (X,Y)) (𝟙 (U.obj Z))) ≫
      αS.hom.app ((U.obj X,U.obj Y),U.obj Z)) ∧
  (∀ X Y : D,
    U.map (σR.hom.app (X,Y)) ≫ μ.hom.app (Y,X) =
      μ.hom.app (X,Y) ≫ σS.hom.app (U.obj X,U.obj Y)) ∧
  ∀ (a b : ℤ) (X Y : D),
    U.map ((tR a b).hom.app (X,Y)) ≫
      (U.commShiftIso (a + b)).hom.app (T.obj (X,Y)) ≫
      (shiftFunctor E (a + b)).map (μ.hom.app (X,Y)) =
    μ.hom.app (X⟦a⟧,Y⟦b⟧) ≫
      TS.map (Prod.mkHom ((U.commShiftIso a).hom.app X)
        ((U.commShiftIso b).hom.app Y)) ≫
      (tS a b).hom.app (U.obj X,U.obj Y)

end PullbackPredicates

section BinaryNormalization
variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
  {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
  (q : A ⥤ D) [q.CommShift ℤ] (P : ObjectProperty A)
  (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)

/-- The representative normalization of a tensor symmetry.
Source: Stacks 0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def TensorSymmetryNormalization
    (H : ∀ E F : A, (t.obj (E, F) ≅ t.obj (F, E)) → Prop)
    (σ : T ≅ CategoryTheory.Prod.swap D D ⋙ T) : Prop :=
  ∀ (E F : A) (hE : P E) (hF : P F),
    ∃ χ : t.obj (E, F) ≅ t.obj (F, E), H E F χ ∧
      r.hom.app (⟨E, hE⟩, ⟨F, hF⟩) ≫ σ.hom.app (q.obj E, q.obj F) =
        q.map χ.hom ≫ r.hom.app (⟨F, hF⟩, ⟨E, hE⟩)
end BinaryNormalization

private theorem descendTensorSwapNormalized
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (c : t ≅ CategoryTheory.Prod.swap A A ⋙ t)
    (H : ∀ E F : A, (t.obj (E, F) ≅ t.obj (F, E)) → Prop)
    (hc : ∀ E F, H E F (c.app (E, F)))
    (huniq : ∀ (E F : A) (χ χ' : t.obj (E, F) ≅ t.obj (F, E)),
      H E F χ → H E F χ' → χ = χ')
    (hex : ∀ (U V : D × D ⥤ D)
      (e : ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ U ≅
        ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F : P.FullSubcategory,
        s.app (q.obj E.obj, q.obj F.obj) = e.app (E, F))
    (hext : ∀ {U V : D × D ⥤ D} (s s' : U ≅ V),
      (∀ E F : P.FullSubcategory, s.app (q.obj E.obj, q.obj F.obj) =
        s'.app (q.obj E.obj, q.obj F.obj)) → s = s') :
    ∃! σ : T ≅ CategoryTheory.Prod.swap D D ⋙ T,
      TensorSymmetryNormalization q P t T r H σ := by
  obtain ⟨σ, hs, hu⟩ := descendTensorSwap q P t T r c hex hext
  refine ⟨σ, ?_, ?_⟩
  · intro E F hE hF
    exact ⟨c.app (E, F), hc E F, hs E F hE hF⟩
  · intro σ' hσ'
    apply hu σ'
    intro E F hE hF
    obtain ⟨χ, hχ, h⟩ := hσ' E F hE hF
    have he := huniq E F χ (c.app (E, F)) hχ (hc E F)
    subst χ
    exact h


section NormalizationPredicates
variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
  (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
  (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)

/-- A tensor associator is normalized by its representative square.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def TensorAssociatorNormalization
    (H : ∀ E F G : A, (t.obj (t.obj (E, F), G) ≅ t.obj (E, t.obj (F, G))) → Prop)
    (α : (T.prod (𝟭 D)) ⋙ T ≅
      CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T) : Prop :=
  ∀ (E F G : A) (hE : P E) (hF : P F) (hG : P G),
    ∃ (hEF : P (t.obj (E, F))) (hFG : P (t.obj (F, G)))
      (χ : t.obj (t.obj (E, F), G) ≅ t.obj (E, t.obj (F, G))),
      H E F G χ ∧
      r.hom.app (⟨_, hEF⟩, ⟨G, hG⟩) ≫
        T.map (Prod.mkHom (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) (𝟙 (q.obj G))) ≫
        α.hom.app ((q.obj E, q.obj F), q.obj G) =
      q.map χ.hom ≫ r.hom.app (⟨E, hE⟩, ⟨_, hFG⟩) ≫
        T.map (Prod.mkHom (𝟙 (q.obj E)) (r.hom.app (⟨F, hF⟩, ⟨G, hG⟩)))
end NormalizationPredicates

/-- A tensor functor with its natural resolving comparison. -/
structure ResolvingTensorModel
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) where
  tensor : D × D ⥤ D
  representative : (P.ι.prod P.ι) ⋙ t ⋙ q ≅
    ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ tensor

private theorem descendTensorAssociatorNormalized
    {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    (q : A ⥤ D) (P : ObjectProperty A) (t : A × A ⥤ A) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (hclosed : ∀ E F : P.FullSubcategory, P (t.obj (E.obj, F.obj)))
    (c : (t.prod (𝟭 A)) ⋙ t ≅
      CategoryTheory.prod.associator A A A ⋙ ((𝟭 A).prod t) ⋙ t)
    (H : ∀ E F G : A, (t.obj (t.obj (E, F), G) ≅ t.obj (E, t.obj (F, G))) → Prop)
    (hc : ∀ E F G, H E F G (c.app ((E, F), G)))
    (huniq : ∀ (E F G : A) (χ χ' : t.obj (t.obj (E, F), G) ≅
        t.obj (E, t.obj (F, G))), H E F G χ → H E F G χ' → χ = χ')
    (hex : ∀ (U V : (D × D) × D ⥤ D)
      (e : (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ U ≅
        (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) = e.app ((E, F), G))
    (hext : ∀ {U V : (D × D) × D ⥤ D} (s s' : U ≅ V),
      (∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) =
          s'.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj)) → s = s') :
    ∃! α : (T.prod (𝟭 D)) ⋙ T ≅
        CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T,
      TensorAssociatorNormalization q P t T r H α := by
  let m : P.FullSubcategory × P.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift ((P.ι.prod P.ι) ⋙ t) (fun E ↦ hclosed E.1 E.2)
  let l := isoWhiskerLeft (m.prod (𝟭 _)) r ≪≫
    isoWhiskerRight (NatIso.prod r (Iso.refl (P.ι ⋙ q))) T
  let rr := isoWhiskerLeft (CategoryTheory.prod.associator
      P.FullSubcategory P.FullSubcategory P.FullSubcategory)
    (isoWhiskerLeft ((𝟭 _).prod m) r ≪≫
      isoWhiskerRight (NatIso.prod (Iso.refl (P.ι ⋙ q)) r) T)
  let e := l.symm ≪≫
    isoWhiskerRight (isoWhiskerLeft ((P.ι.prod P.ι).prod P.ι) c) q ≪≫ rr
  obtain ⟨α, hα⟩ := hex ((T.prod (𝟭 D)) ⋙ T)
    (CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T) e
  have hn (E F G : P.FullSubcategory) :
      r.hom.app (m.obj (E, F), G) ≫
        T.map (Prod.mkHom (r.hom.app (E, F)) (𝟙 (q.obj G.obj))) ≫
        α.hom.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) =
      q.map (c.hom.app ((E.obj, F.obj), G.obj)) ≫
        r.hom.app (E, m.obj (F, G)) ≫
        T.map (Prod.mkHom (𝟙 (q.obj E.obj)) (r.hom.app (F, G))) := by
    have ha := congrArg Iso.hom (hα E F G)
    change α.hom.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) = _ at ha
    rw [ha]
    rw [← Category.assoc]
    change l.hom.app ((E, F), G) ≫ e.hom.app ((E, F), G) = _
    simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Iso.hom_inv_id_app_assoc, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      whiskerLeft_app, whiskerRight_app]
    rfl
  refine ⟨α, ?_, ?_⟩
  · intro E F G hE hF hG
    exact ⟨hclosed ⟨E, hE⟩ ⟨F, hF⟩, hclosed ⟨F, hF⟩ ⟨G, hG⟩,
      c.app ((E, F), G), hc E F G, hn ⟨E, hE⟩ ⟨F, hF⟩ ⟨G, hG⟩⟩
  · intro α' hα'
    apply hext
    rintro ⟨E, hE⟩ ⟨F, hF⟩ ⟨G, hG⟩
    apply Iso.ext
    obtain ⟨hEF, hFG, χ, hχ, h⟩ := hα' E F G hE hF hG
    have he := huniq E F G χ (c.app ((E, F), G)) hχ (hc E F G)
    subst χ
    have : IsIso (Prod.mkHom (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) (𝟙 (q.obj G))) :=
      (Iso.prod (r.app (⟨E, hE⟩, ⟨F, hF⟩)) (Iso.refl (q.obj G))).isIso_hom
    apply (cancel_epi (T.map (Prod.mkHom
      (r.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) (𝟙 (q.obj G))))).1
    apply (cancel_epi (r.hom.app (⟨t.obj (E, F), hEF⟩, ⟨G, hG⟩))).1
    exact h.trans (hn ⟨E, hE⟩ ⟨F, hF⟩ ⟨G, hG⟩).symm

section ComplexFormulaPredicates
variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  [HasZeroObject A] [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
  [∀ E F : CochainComplex A ℤ, HomologicalComplex.HasTensor E F]
  [∀ E F G : CochainComplex A ℤ, HomologicalComplex.HasGoodTensor₁₂ E F G]

/-- Signed swap on total complexes, characterized on every summand. These equations
specify an actual map, including its sign; existence is part of the derived normalization.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ComplexTensorSwapFormula (E F : CochainComplex A ℤ)
    (χ : (HomologicalComplex.tensorObj E F) ≅ (HomologicalComplex.tensorObj F E)) : Prop :=
  ∀ p q : ℤ,
    CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl ≫
      χ.hom.f (p + q) =
    ((-1 : ℤ) ^ Int.natAbs (p * q)) •
      ((β_ (E.X p) (F.X q)).hom ≫
        CochainComplex.ιMapBifunctor F E (curriedTensor A) q p (p + q)
          (add_comm q p))

/-- The unsigned associator is fixed on triple total summands.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ComplexTensorAssociatorFormula (E F G : CochainComplex A ℤ)
    (χ : (HomologicalComplex.tensorObj (HomologicalComplex.tensorObj E F) G) ≅
      (HomologicalComplex.tensorObj E (HomologicalComplex.tensorObj F G))) : Prop :=
  ∀ p q r : ℤ,
    ((curriedTensor A).map
      (CochainComplex.ιMapBifunctor E F (curriedTensor A) p q (p + q) rfl)).app _ ≫
      CochainComplex.ιMapBifunctor ((HomologicalComplex.tensorObj E F)) G
        (curriedTensor A) (p + q) r ((p + q) + r) rfl ≫
      χ.hom.f ((p + q) + r) =
    (α_ (E.X p) (F.X q) (G.X r)).hom ≫
      ((curriedTensor A).obj (E.X p)).map
        (CochainComplex.ιMapBifunctor F G (curriedTensor A) q r (q + r) rfl) ≫
      CochainComplex.ιMapBifunctor E ((HomologicalComplex.tensorObj F G))
        (curriedTensor A) p (q + r) ((p + q) + r) (add_assoc p q r).symm

end ComplexFormulaPredicates

section
variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  [HasZeroObject A] [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ E F : GradedObject ℤ A, GradedObject.HasTensor E F]
  [∀ E F G : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor E F G]
  [∀ E F G : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ E F G]

private theorem descendTotalAssociator
    {D : Type u₂} [Category.{v₂} D] (q : CochainComplex A ℤ ⥤ D)
    (P : ObjectProperty (CochainComplex A ℤ)) (T : D × D ⥤ D)
    (r : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj (curriedTensor A).map₂CochainComplex ⋙ q ≅
      ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T)
    (hc : ∀ E F : P.FullSubcategory, P (HomologicalComplex.tensorObj E.obj F.obj))
    (hex : ∀ (U V : (D × D) × D ⥤ D)
      (e : (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ U ≅
        (((P.ι ⋙ q).prod (P.ι ⋙ q)).prod (P.ι ⋙ q)) ⋙ V),
      ∃ s : U ≅ V, ∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) = e.app ((E, F), G))
    (hext : ∀ {U V : (D × D) × D ⥤ D} (s s' : U ≅ V),
      (∀ E F G : P.FullSubcategory,
        s.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj) =
          s'.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj)) → s = s') :
    ∃! α : (T.prod (𝟭 D)) ⋙ T ≅
        CategoryTheory.prod.associator D D D ⋙ ((𝟭 D).prod T) ⋙ T,
      TensorAssociatorNormalization q P
        (Functor.uncurry.obj (curriedTensor A).map₂CochainComplex) T r
        (ComplexTensorAssociatorFormula (A := A)) α := by
  let t := Functor.uncurry.obj (curriedTensor A).map₂CochainComplex
  let c : (t.prod (𝟭 _)) ⋙ t ≅
      CategoryTheory.prod.associator _ _ _ ⋙ ((𝟭 _).prod t) ⋙ t := by
    have hm {E E' F F' : CochainComplex A ℤ} (f : E ⟶ E') (g : F ⟶ F') :
        t.map (Prod.mkHom f g) = HomologicalComplex.tensorHom f g := by
      simp [t, Functor.map₂HomologicalComplex, Functor.uncurry_obj_map,
        HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
    refine NatIso.ofComponents (F := (t.prod (𝟭 _)) ⋙ t)
      (G := CategoryTheory.prod.associator _ _ _ ⋙ ((𝟭 _).prod t) ⋙ t)
      (fun E ↦ HomologicalComplex.associator E.1.1 E.1.2 E.2) ?_
    intro E F f
    change t.map (Prod.mkHom (t.map (Prod.mkHom f.1.1 f.1.2)) f.2) ≫ _ =
      _ ≫ t.map (Prod.mkHom f.1.1 (t.map (Prod.mkHom f.1.2 f.2)))
    rw [hm, hm, hm, hm]
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrFun (GradedObject.Monoidal.associator_naturality
      f.1.1.f f.1.2.f f.2.f) n
  have hf (E F G : CochainComplex A ℤ) :
      ComplexTensorAssociatorFormula E F G (c.app ((E, F), G)) := by
    change ComplexTensorAssociatorFormula E F G (HomologicalComplex.associator E F G)
    intro p q r
    have h := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
      (MonoidalCategory.curriedAssociatorNatIso A) E F G (.up ℤ) (.up ℤ) (.up ℤ)
      p q r ((p + q) + r) rfl
    rw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor A) (curriedTensor A)
      E F G (.up ℤ) (.up ℤ) p q r (p + q) ((p + q) + r) rfl rfl] at h
    rw [HomologicalComplex.mapBifunctor₂₃.ι_eq (curriedTensor A) (curriedTensor A)
      E F G (.up ℤ) (.up ℤ) (.up ℤ) p q r (q + r) ((p + q) + r) rfl
      (add_assoc p q r).symm] at h
    simp only [HomologicalComplex.associator, HomologicalComplex.mapBifunctorAssociator,
      HomologicalComplex.Hom.isoOfComponents, MonoidalCategory.curriedAssociatorNatIso,
      NatIso.ofComponents, CochainComplex.ιMapBifunctor, HomologicalComplex.tensorObj,
      Category.assoc] at h ⊢
    exact h
  have hu (E F G : CochainComplex A ℤ)
      (χ χ' : HomologicalComplex.tensorObj (HomologicalComplex.tensorObj E F) G ≅
        HomologicalComplex.tensorObj E (HomologicalComplex.tensorObj F G))
      (hχ : ComplexTensorAssociatorFormula E F G χ)
      (hχ' : ComplexTensorAssociatorFormula E F G χ') : χ = χ' := by
    apply Iso.ext
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex.mapBifunctor₁₂.hom_ext
      (F₁₂ := curriedTensor A) (G := curriedTensor A)
      (K₁ := E) (K₂ := F) (K₃ := G) (c₁₂ := .up ℤ) (c₄ := .up ℤ)
    intro p q r hn
    change p + q + r = n at hn
    subst n
    erw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor A) (curriedTensor A)
      E F G (.up ℤ) (.up ℤ) p q r (p + q) ((p + q) + r) rfl rfl]
    simp only [Category.assoc]
    exact (hχ p q r).trans (hχ' p q r).symm
  exact descendTensorAssociatorNormalized q P _ T r hc c
    (ComplexTensorAssociatorFormula (A := A)) hf hu hex hext

end



section SignedCoherenceProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
private theorem symmetryDiagram
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    {A A' B B' U U' V V' : D} (n m : ℤ) (h : m = n) (z : ℤ)
    (r : A ⟶ U) [Epi r] (r' : A' ⟶ U') (s : B ⟶ V) (s' : B' ⟶ V')
    (t : U ⟶ V⟦n⟧) (t' : U' ⟶ V'⟦m⟧)
    (σ : V ⟶ V') (σ' : U ⟶ U')
    (c : A ⟶ B⟦n⟧) (c' : A' ⟶ B'⟦m⟧) (χ : A ⟶ A') (ψ : B ⟶ B')
    (ht : r ≫ t = c ≫ (shiftFunctor D n).map s)
    (ht' : r' ≫ t' = c' ≫ (shiftFunctor D m).map s')
    (hs : s ≫ σ = ψ ≫ s') (hs' : r ≫ σ' = χ ≫ r')
    (hc : c ≫ (shiftFunctor D n).map ψ =
      z • (χ ≫ c' ≫ eqToHom (congrArg (fun k : ℤ ↦ B'⟦k⟧) h))) :
    t ≫ (shiftFunctor D n).map σ =
      z • (σ' ≫ t' ≫ eqToHom (congrArg (fun k : ℤ ↦ V'⟦k⟧) h)) := by
  have he : eqToHom (congrArg (fun k : ℤ ↦ B'⟦k⟧) h) ≫
      (shiftFunctor D n).map s' = (shiftFunctor D m).map s' ≫
        eqToHom (congrArg (fun k : ℤ ↦ V'⟦k⟧) h) := by
    subst n
    simp
  apply (cancel_epi r).1
  calc
    r ≫ (t ≫ (shiftFunctor D n).map σ) =
        c ≫ (shiftFunctor D n).map ψ ≫ (shiftFunctor D n).map s' := by
      rw [← Category.assoc, ht, Category.assoc, ← Functor.map_comp, hs, Functor.map_comp]
    _ = z • (χ ≫ c' ≫ eqToHom (congrArg (fun k : ℤ ↦ B'⟦k⟧) h) ≫
        (shiftFunctor D n).map s') := by
      rw [← Category.assoc, hc, Preadditive.zsmul_comp]
      simp only [Category.assoc]
    _ = z • (χ ≫ r' ≫ t' ≫ eqToHom (congrArg (fun k : ℤ ↦ V'⟦k⟧) h)) := by
      congr 1
      rw [he, ← reassoc_of% ht']
    _ = r ≫ (z • (σ' ≫ t' ≫ eqToHom (congrArg (fun k : ℤ ↦ V'⟦k⟧) h))) := by
      rw [Preadditive.comp_zsmul]
      congr 1
      rw [← reassoc_of% hs']

private theorem mapShiftEqToHom
    {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ]
    {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ]
    (q : A ⥤ D) [q.CommShift ℤ] (X : A) (n m : ℤ) (h : n = m) :
    q.map (eqToHom (congrArg (fun k : ℤ ↦ X⟦k⟧) h)) ≫
        (q.commShiftIso m).hom.app X =
      (q.commShiftIso n).hom.app X ≫
        eqToHom (congrArg (fun k : ℤ ↦ (q.obj X)⟦k⟧) h) := by
  subst m
  simp

private theorem pairShift_compatibility
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    (T : A ⥤ A ⥤ A) (V : B ⥤ B ⥤ B) (F : A ⥤ B)
    [T.CommShift₂Int] [V.CommShift₂Int] [F.CommShift ℤ]
    (m : ∀ X Y : A, F.obj ((T.obj X).obj Y) ⟶ (V.obj (F.obj X)).obj (F.obj Y))
    (hr : ∀ (n : ℤ) (X Y : A), m (X⟦n⟧) Y ≫
      (V.map ((F.commShiftIso n).hom.app X)).app (F.obj Y) ≫
      ((V.flip.obj (F.obj Y)).commShiftIso n).hom.app (F.obj X) =
      F.map (((T.flip.obj Y).commShiftIso n).hom.app X) ≫
      (F.commShiftIso n).hom.app ((T.obj X).obj Y) ≫ (m X Y)⟦n⟧')
    (hl : ∀ (n : ℤ) (X Y : A), m X (Y⟦n⟧) ≫
      (V.obj (F.obj X)).map ((F.commShiftIso n).hom.app Y) ≫
      ((V.obj (F.obj X)).commShiftIso n).hom.app (F.obj Y) =
      F.map (((T.obj X).commShiftIso n).hom.app Y) ≫
      (F.commShiftIso n).hom.app ((T.obj X).obj Y) ≫ (m X Y)⟦n⟧')
    (a b : ℤ) (X Y : A) :
    m (X⟦a⟧) (Y⟦b⟧) ≫ (Functor.uncurry.obj V).map
        (Prod.mkHom ((F.commShiftIso a).hom.app X) ((F.commShiftIso b).hom.app Y)) ≫
      (tensorPairShift V a b).hom.app (F.obj X, F.obj Y) =
    F.map ((tensorPairShift T a b).hom.app (X, Y)) ≫
      (F.commShiftIso (a + b)).hom.app ((T.obj X).obj Y) ≫ (m X Y)⟦a + b⟧' := by
  simp only [tensorPairShift, tensorRightShift, tensorLeftShift, Iso.trans_hom,
    Iso.app_hom, Functor.uncurry_obj_obj,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, NatIso.ofComponents_hom_app, Iso.symm_hom]
  have hx := (NatTrans.shift_app_comm
    (V.map ((F.commShiftIso a).hom.app X)) b (F.obj Y)).symm
  change (V.map ((F.commShiftIso a).hom.app X)).app ((F.obj Y)⟦b⟧) ≫
      ((V.obj ((F.obj X)⟦a⟧)).commShiftIso b).hom.app (F.obj Y) =
    ((V.obj (F.obj (X⟦a⟧))).commShiftIso b).hom.app (F.obj Y) ≫
      (shiftFunctor _ b).map ((V.map ((F.commShiftIso a).hom.app X)).app (F.obj Y)) at hx
  have hnat := (F.commShiftIso b).hom.naturality (((T.flip.obj Y).commShiftIso a).hom.app X)
  change F.map ((shiftFunctor A b).map
      (((T.flip.obj Y).commShiftIso a).hom.app X)) ≫
      (F.commShiftIso b).hom.app (((T.obj X).obj Y)⟦a⟧) =
    (F.commShiftIso b).hom.app ((T.obj (X⟦a⟧)).obj Y) ≫
      (shiftFunctor B b).map (F.map (((T.flip.obj Y).commShiftIso a).hom.app X)) at hnat
  have hadd := NatTrans.congr_app
    (congrArg Iso.hom (F.commShiftIso_add' (rfl : a + b = a + b))) ((T.obj X).obj Y)
  simp only [Functor.CommShift.isoAdd'_hom_app,
    shiftFunctorAdd'_eq_shiftFunctorAdd] at hadd
  have hsum : (F.commShiftIso b).hom.app (((T.obj X).obj Y)⟦a⟧) ≫
      ((F.commShiftIso a).hom.app ((T.obj X).obj Y))⟦b⟧' ≫
      (shiftFunctorAdd _ a b).inv.app (F.obj ((T.obj X).obj Y)) =
    F.map ((shiftFunctorAdd _ a b).inv.app ((T.obj X).obj Y)) ≫
      (F.commShiftIso (a + b)).hom.app ((T.obj X).obj Y) := by
    rw [hadd]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  have hmadd := (shiftFunctorAdd B a b).inv.naturality (m X Y)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj] at hmadd
  rw [Functor.uncurry_obj_map]
  rw [← (V.map ((F.commShiftIso a).hom.app X)).naturality
    ((F.commShiftIso b).hom.app Y)]
  dsimp only [Functor.comp_obj, Functor.prod_obj, CategoryTheory.Functor.id_obj]
  simp only [Category.assoc]
  rw [reassoc_of% hx, reassoc_of% (hl b (X⟦a⟧) Y)]
  rw [← (shiftFunctor _ b).map_comp_assoc, ← (shiftFunctor _ b).map_comp_assoc]
  simp only [Category.assoc]
  rw [hr]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnat, hmadd, reassoc_of% hsum]


universe uC vC uD vD r
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
attribute [local irreducible] SheafOfModules.monoidalCategory
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
attribute [local implicit_reducible] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local instance 2000] tensorAdditive tensorObjAdditive tensorHasMapBifunctor
attribute [local irreducible] CategoryTheory.CommShift₂Setup.int
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjMap₂CochainComplex
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjFlipMap₂CochainComplex
set_option maxHeartbeats 800000 in
-- Keep the independent coefficient universes explicit in the comparison interface.
private theorem complex_pairShift_compatibility
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
    (f : RingedPullback R S) (k : Comparison f)
    (a b : ℤ) (E F : CochainComplex (Modules R) ℤ) :
    (comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k (E⟦a⟧) (F⟦b⟧)).hom ≫
      (Functor.uncurry.obj (totalTensor.{uD, vD, r} S)).map
        (Prod.mkHom (((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f).commShiftIso
          a).hom.app E)
          (((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f).commShiftIso b).hom.app
            F)) ≫
      (tensorPairShift (totalTensor.{uD, vD, r} S) a b).hom.app ((pull.{r, uC, vC, uD, vD} (J := J)
        (K := K) (R := R) (S := S) f).obj E, (pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S
        := S) f).obj F) =
    (pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f).map ((tensorPairShift
      (totalTensor.{uC, vC, r} R) a b).hom.app (E, F)) ≫
      ((pull.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f).commShiftIso (a +
        b)).hom.app (((totalTensor.{uC, vC, r} R).obj E).obj F) ≫
      (shiftFunctor _ (a + b)).map (comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S :=
        S) f k E F).hom := by
  have h := tensorComparison_commShift.{uC, vC, uD, vD, r} (J := J) (K := K) (R := R) (S := S) f k
  let t := tensorComparisonNatTrans.{uC, vC, uD, vD, r} (J := J) (K := K) (R := R) (S := S) f k
  have hr (n : ℤ) (X Y : CochainComplex (Modules R) ℤ) := by
    let chi : (totalTensor.{uC, vC, r} R).flip.obj Y ⋙ (pull f) ⟶
        (pull f) ⋙ (totalTensor.{uD, vD, r} S).flip.obj ((pull f).obj Y) := t.flipApp Y
    letI : chi.CommShift ℤ := h.2 Y
    exact (NatTrans.shift_app_comm chi n X).symm
  have hl (n : ℤ) (X Y : CochainComplex (Modules R) ℤ) := by
    let chi : (totalTensor.{uC, vC, r} R).obj X ⋙ (pull f) ⟶
        (pull f) ⋙ (totalTensor.{uD, vD, r} S).obj ((pull f).obj X) := t.app X
    letI : chi.CommShift ℤ := h.1 X
    exact (NatTrans.shift_app_comm chi n Y).symm
  apply pairShift_compatibility (totalTensor.{uC, vC, r} R) (totalTensor.{uD, vD, r} S) (pull.{r,
    uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f)
    (fun X Y ↦ (comparison.{r, uC, vC, uD, vD} (J := J) (K := K) (R := R) (S := S) f k X Y).hom)
  · intro n X Y
    simpa only [Functor.commShiftIso_comp_hom_app, t, tensorComparisonNatTrans,
      NatTrans.flipApp, CategoryTheory.flipFunctor, Functor.flip, Functor.comp_obj, Category.assoc]
        using hr n X Y
  · intro n X Y
    simpa only [Functor.commShiftIso_comp_hom_app, t, tensorComparisonNatTrans,
      Category.assoc] using hl n X Y


end SignedCoherenceProofs

namespace SheafOfModules
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  Functor.mapHomologicalComplex Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
  CochainComplex.Monoidal.braiding

/-- The module category on the ringed site. Source: Stacks 03DA
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedModuleCategory {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v}) :=
  CategoryTheory.ringedSiteModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- Its unbounded derived category. Source: Stacks 05RR
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedDerivedCategory {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (ShiftedModuleCategory R)] :=
  DerivedCategory (ShiftedModuleCategory R)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory R)]

/-- Flat-term K-flat resolving complexes. Source: Stacks 06YS and 06YU
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorResolving : ObjectProperty (CochainComplex (ShiftedModuleCategory R) ℤ) :=
  fun E ↦ E.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (E.X n)

/-- The ordinary tensor bifunctor, with the dependency's canonical sheaf tensor.
Source: Stacks 03EK (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedOrdinaryTensor :=
  @curriedTensor (ShiftedModuleCategory R) _ (monoidalCategory R)

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
theorem shiftedOrdinaryTensor_additive : (shiftedOrdinaryTensor R).Additive := by
  exact KFlatFixedTensor.tensorAdditive R

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
theorem shiftedOrdinaryTensor_objAdditive (X : ShiftedModuleCategory R) :
    ((shiftedOrdinaryTensor R).obj X).Additive := by
  exact KFlatFixedTensor.tensorObjAdditive R X

attribute [local instance 4001] shiftedOrdinaryTensor_additive
  shiftedOrdinaryTensor_objAdditive

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
theorem shiftedOrdinaryTensor_totalExists
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    CochainComplex.HasMapBifunctor E F (shiftedOrdinaryTensor R) := by
  exact KFlatFixedTensor.tensorHasMapBifunctor R E F

attribute [local instance 4001] shiftedOrdinaryTensor_totalExists

/-- Total tensor, with the differential sign on the second factor.
Source: Stacks 06YM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTotalTensor :=
  Functor.uncurry.obj (shiftedOrdinaryTensor R).map₂CochainComplex

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
private theorem shiftedTotalTensor_obj
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    (shiftedTotalTensor R).obj (E, F) =
      CochainComplex.mapBifunctor E F (shiftedOrdinaryTensor R) := rfl

/-- A presentation of the derived tensor by the natural resolving comparison.
This is precisely the tensor and its representative isomorphism from site-derived-tensor
 descent; quantifying over presentations makes the statement independent of this choice.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev ShiftedTensorModel :=
  ResolvingTensorModel DerivedCategory.Q (shiftedTensorResolving R) (shiftedTotalTensor R)

/-- The recorded site-derived tensor admits exactly the resolving presentation used here.
This connects the presentation-independent calculus to the dependency's actual bifunctor.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Step 3): take the tensor and homotopy representative comparison from
site_derived_tensor_descent_independentCoefficients. Precompose its two comparisons
with the resolving complexes' homotopy quotient and compose with quotientCompQhIso.
The membership equivalence identifies precisely the K-flat flat-term objects.
The resulting natural comparison supplies the displayed model of the recorded tensor. -/
theorem shiftedTensorPublishedModel_exists :
    ∃ T : ShiftedTensorModel R,
      T.tensor = siteDerivedTensorIndependentCoefficients J R := by
  refine ⟨⟨siteDerivedTensorIndependentCoefficients J R, ?_⟩, rfl⟩
  let q : (shiftedTensorResolving R).ι ⋙
      HomotopyCategory.quotient (ShiftedModuleCategory R) (.up ℤ) ⋙
        DerivedCategory.Qh ≅ (shiftedTensorResolving R).ι ⋙ DerivedCategory.Q :=
    isoWhiskerLeft (shiftedTensorResolving R).ι
      (DerivedCategory.quotientCompQhIso (ShiftedModuleCategory R))
  exact isoWhiskerLeft ((shiftedTensorResolving R).ι.prod (shiftedTensorResolving R).ι)
      (isoWhiskerLeft (shiftedTotalTensor R)
        (DerivedCategory.quotientCompQhIso (ShiftedModuleCategory R))).symm ≪≫
    DerivedTensorConstraints.genericPresentationComparison (shiftedTensorResolving R).ι
      (KFlatFixedTensor.selectedTensorPresentation R)
      (fun E ↦ (KFlatFixedTensor.resolvingProperty_spec R _).2 E.property) ≪≫
    isoWhiskerRight (NatIso.prod q q) (siteDerivedTensorIndependentCoefficients J R)

@[irreducible]
def shiftedTensorComplexComparisonNatIso (a b : ℤ) :
    ((shiftFunctor (CochainComplex (ShiftedModuleCategory R) ℤ) a).prod
      (shiftFunctor _ b)) ⋙ shiftedTotalTensor R ≅
    shiftedTotalTensor R ⋙ shiftFunctor _ (a + b) :=
  totalTensorPairShift (shiftedOrdinaryTensor R) a b

/-- Move the second shift first, then the first shift. Thus the only sign is
`(-1)^(bp)` with p the degree in E[a], exactly the node's convention.
Source: Stacks sign rules, item-shift-tensor
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorComplexComparison
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (a b : ℤ) :
    (shiftedTotalTensor R).obj (E⟦a⟧, F⟦b⟧) ≅
      ((shiftedTotalTensor R).obj (E, F))⟦a + b⟧ :=
  (shiftedTensorComplexComparisonNatIso R a b).app (E, F)

variable (T : ShiftedTensorModel R)

/-- Normalization of t on every resolving model, with localization's shift comparisons.
Source: Stacks 06YU and sign rules (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalShiftComparison (a b : ℤ)
    (t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod
      (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅
      T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b)) : Prop :=
  TensorShiftNormalization DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative a b
    (shiftedTensorComplexComparisonNatIso R a b) t

attribute [local irreducible] TensorShiftNormalization TensorSymmetryNormalization
  TensorAssociatorNormalization GenericTensorPullbackCoherence

attribute [local irreducible] siteDerivedTensorIndependentCoefficients

private theorem shiftedModelShift_closed
    (E : (shiftedTensorResolving R).FullSubcategory) (n : ℤ) :
    shiftedTensorResolving R (E.obj⟦n⟧) := by
  exact (DerivedTensorConstraints.derived_tensor_model_closure R).2.1 ⟨E.obj, E.property⟩ n

/-- The canonical comparison is uniquely determined by the resolving square.
Source: Stacks 06YU; proof Steps 1--3 of the node
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof: the two complex shift isomorphisms give the coefficient (-1)^(bp), and are natural.
Shifts preserve K-flatness and flat terms (Step 2). Transport through the representative
comparison and extend the resulting transformation and its inverse by the unique-extension
clause of site-derived-tensor descent (Step 3). Uniqueness proves the inverse equations
and the asserted uniqueness. -/
theorem shiftedTensorCanonicalComparison_exists (a b : ℤ) :
    ∃! t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod
      (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅
      T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b),
      IsCanonicalShiftComparison R T a b t := by
  exact descendTensorShiftAPI DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative (shiftedModelShift_closed R)
    (DerivedTensorConstraints.extendBinary R)
    (fun _ _ h ↦ DerivedTensorConstraints.binary_iso_ext R _ _ h)
    a b (shiftedTensorComplexComparisonNatIso R a b)


/-- The comparison fixed by the actual resolving square, not a free parameter.
Source: Stacks 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorCanonicalComparison (a b : ℤ) :
    ((shiftFunctor (ShiftedDerivedCategory R) a).prod (shiftFunctor _ b)) ⋙ T.tensor ≅
      T.tensor ⋙ shiftFunctor _ (a + b) :=
  (shiftedTensorCanonicalComparison_exists R T a b).exists.choose

attribute [local irreducible] shiftedTensorCanonicalComparison

/-- Signed swap on total complexes, characterized on every summand. These equations
specify an actual map, including its sign; existence is part of the derived normalization.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsSignedComplexSwap (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E)) : Prop :=
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  ComplexTensorSwapFormula E F χ

/-- Derived symmetry is the image of the signed swap on K-flat representatives.
Source: Stacks 0FPQ and 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalDerivedTensorSymmetry
    (σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor) : Prop :=
  TensorSymmetryNormalization DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative (IsSignedComplexSwap R) σ

private def shiftedComplexSwap
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E) :=
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  totalComplexSwap E F

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
private theorem shiftedComplexSwap_signed (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    IsSignedComplexSwap R E F (shiftedComplexSwap R E F) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  intro p q
  exact totalComplexSwap_signed E F p q

omit [HasDerivedCategory.{w} (ShiftedModuleCategory R)] in
private theorem shiftedComplexSwap_unique (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ χ' : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E))
    (hχ : IsSignedComplexSwap R E F χ) (hχ' : IsSignedComplexSwap R E F χ') : χ = χ' := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  subst n
  exact (hχ p q).trans (hχ' p q).symm

/-- Existence and uniqueness of the signed derived symmetry.
Source: Stacks 0FPQ and 06YU (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Step 3): define the swap by its summand equations. The differential coefficients
of y tensor dx agree modulo 2, as do those of dy tensor x. The reverse swap is its inverse.
It is natural; descend it and its inverse using the unique-extension clause of tensor descent.
The summand equations determine the chain map and descent determines the natural isomorphism. -/
theorem derivedTensorSymmetry_exists :
    ∃! σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor,
      IsCanonicalDerivedTensorSymmetry R T σ := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  let c : shiftedTotalTensor R ≅ CategoryTheory.Prod.swap _ _ ⋙ shiftedTotalTensor R :=
    totalSwapNatIso (shiftedComplexSwap R) (shiftedComplexSwap_signed R)
  exact descendTensorSwapNormalized DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative c (IsSignedComplexSwap R)
    (by
      intro E F
      have he : c.app (E, F) = shiftedComplexSwap R E F := by
        apply Iso.ext
        exact totalSwapNatIso_hom_app (shiftedComplexSwap R)
          (shiftedComplexSwap_signed R) E F
      rw [he]
      exact shiftedComplexSwap_signed R E F)
    (shiftedComplexSwap_unique R) (DerivedTensorConstraints.extendBinary R)
    (fun _ _ h ↦ DerivedTensorConstraints.binary_iso_ext R _ _ h)


/-- Canonical Koszul symmetry, fixed by the signed representative equations.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def derivedTensorSymmetry :
    T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor :=
  (derivedTensorSymmetry_exists R T).exists.choose

attribute [local irreducible] derivedTensorSymmetry

/-- B is tensor of the two maps followed by the canonical shift comparison.
Source: Stacks 0FPL/0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedTensorB (a b : ℤ) (P Q K L : ShiftedDerivedCategory R)
    (f : P ⟶ K⟦a⟧) (g : Q ⟶ L⟦b⟧) :
    T.tensor.obj (P, Q) ⟶ (T.tensor.obj (K, L))⟦a + b⟧ :=
  T.tensor.map (Prod.mkHom f g) ≫
    (shiftedTensorCanonicalComparison R T a b).hom.app (K, L)

/-- The unsigned associator is fixed on triple total summands.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsComplexTensorAssociator (E F G : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅
      (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G))) : Prop :=
  letI := monoidalCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  ComplexTensorAssociatorFormula E F G χ

/-- The left triple tensor functor. Source: Stacks 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedTensorLeftTriple := (T.tensor.prod (𝟭 _)) ⋙ T.tensor

/-- The right triple tensor functor. Source: Stacks 0FPQ
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedTensorRightTriple :=
  CategoryTheory.prod.associator (ShiftedDerivedCategory R) _ _ ⋙
    ((𝟭 _).prod T.tensor) ⋙ T.tensor

/-- The derived associator's full representative square, including tensor closure.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def IsCanonicalTensorAssociator
    (α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T) : Prop :=
  TensorAssociatorNormalization DerivedCategory.Q (shiftedTensorResolving R)
    (shiftedTotalTensor R) T.tensor T.representative (IsComplexTensorAssociator R) α

/-- The derived associator exists uniquely with its unsigned normalization.
Source: Stacks 0FPQ/0FPT (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Steps 2--3): tensor preserves sums by its right adjoint, so triple tensor
summands determine the unsigned associator and its inverse. Differential signs are
1, (-1)^p, (-1)^(p+q) on both sides. K-flatness of total tensor follows by applying
K-flatness twice to an acyclic test complex. Tensor products and sums of flat terms
are flat. Extend the representative square and its inverse by tensor descent,
variable by variable. Uniqueness on resolving triples gives uniqueness everywhere. -/
theorem derivedTensorAssociator_exists :
    ∃! α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T,
      IsCanonicalTensorAssociator R T α := by
  let := monoidalCategory R
  let := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  exact descendTotalAssociator DerivedCategory.Q (shiftedTensorResolving R)
    T.tensor T.representative (DerivedTensorConstraints.derived_tensor_model_closure R).1
    (DerivedTensorConstraints.extendTernary R)
    (fun _ _ h ↦ DerivedTensorConstraints.ternary_iso_ext R _ _ h)

/-- Canonical associator, with no arbitrary associator parameter.
Source: Stacks 0FPQ (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def derivedTensorAssociator :
    shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T :=
  (derivedTensorAssociator_exists R T).exists.choose

attribute [local irreducible] derivedTensorAssociator

/-- A module sheaf in degree zero. Source: Stacks 06YU
(blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
abbrev shiftedDegreeZero (P : ShiftedModuleCategory R) : ShiftedDerivedCategory R :=
  (DerivedCategory.singleFunctor _ 0).obj P

/-- Both additivity equations for flat degree-zero sources.
Source: Stacks 0FPL/0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorAdditivityClause (a b : ℤ) : Prop :=
  ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
    ∀ (K L : ShiftedDerivedCategory R)
      (f₁ f₂ : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g₁ g₂ : shiftedDegreeZero R Q ⟶ L⟦b⟧),
      shiftedTensorB R T a b _ _ K L (f₁ + f₂) g₁ =
        shiftedTensorB R T a b _ _ K L f₁ g₁ + shiftedTensorB R T a b _ _ K L f₂ g₁ ∧
      shiftedTensorB R T a b _ _ K L f₁ (g₁ + g₂) =
        shiftedTensorB R T a b _ _ K L f₁ g₁ + shiftedTensorB R T a b _ _ K L f₁ g₂

/-- Associativity for precisely three flat degree-zero source sheaves.
Source: Stacks 0FPL (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorAssociativityClause (a b c : ℤ) : Prop :=
  ∀ (P Q S : ShiftedModuleCategory R),
    IsFlatOnSite P → IsFlatOnSite Q → IsFlatOnSite S →
    ∀ (K L M : ShiftedDerivedCategory R)
      (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g : shiftedDegreeZero R Q ⟶ L⟦b⟧)
      (h : shiftedDegreeZero R S ⟶ M⟦c⟧),
      (derivedTensorAssociator R T).hom.app
          ((shiftedDegreeZero R P, shiftedDegreeZero R Q), shiftedDegreeZero R S) ≫
        shiftedTensorB R T a (b + c) _ _ K (T.tensor.obj (L, M)) f
          (shiftedTensorB R T b c _ _ L M g h) =
      shiftedTensorB R T (a + b) c _ _ (T.tensor.obj (K, L)) M
          (shiftedTensorB R T a b _ _ K L f g) h ≫
        (CategoryTheory.shiftFunctor _ ((a + b) + c)).map
          ((derivedTensorAssociator R T).hom.app ((K, L), M)) ≫
        (eqToIso (congrArg
          (fun n : ℤ ↦ (T.tensor.obj (K, T.tensor.obj (L, M)))⟦n⟧)
          (add_assoc a b c))).hom

/-- Symmetry with the scalar (-1)^(ab) and the specified sum-of-shifts identification.
Source: Stacks 0FPM (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedTensorSymmetryClause (a b : ℤ) : Prop :=
  ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
    ∀ (K L : ShiftedDerivedCategory R)
      (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
      (g : shiftedDegreeZero R Q ⟶ L⟦b⟧),
      shiftedTensorB R T a b _ _ K L f g ≫
        (CategoryTheory.shiftFunctor _ (a + b)).map
          ((derivedTensorSymmetry R T).hom.app (K, L)) =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        ((derivedTensorSymmetry R T).hom.app (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
          shiftedTensorB R T b a _ _ L K g f ≫
          (eqToIso (congrArg (fun n : ℤ ↦ (T.tensor.obj (L, K))⟦n⟧)
            (add_comm b a))).hom)

section SignedMorphismProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance 4001] shiftedOrdinaryTensor_additive
  shiftedOrdinaryTensor_objAdditive shiftedOrdinaryTensor_totalExists
attribute [local instance 4001] DerivedTensorConstraints.complexMonoidal
  DerivedTensorConstraints.complexMonoidalStruct CochainComplex.Monoidal.braidedCategory

attribute [local implicit_reducible] shiftedOrdinaryTensor shiftedTotalTensor
  CategoryTheory.prod.associator

attribute [local semireducible] TensorShiftNormalization TensorSymmetryNormalization
  TensorAssociatorNormalization GenericTensorPullbackCoherence
  siteDerivedTensorIndependentCoefficients shiftedTensorCanonicalComparison
  derivedTensorSymmetry derivedTensorAssociator
private theorem shiftedTensorMap_comp_left
    {X Y Z U V : ShiftedDerivedCategory R} (f : X ⟶ Y) (g : Y ⟶ Z) (h : U ⟶ V) :
    T.tensor.map (Prod.mkHom (f ≫ g) h) =
      T.tensor.map (Prod.mkHom f h) ≫ T.tensor.map (Prod.mkHom g (𝟙 V)) := by
  rw [← T.tensor.map_comp]
  congr 1
  exact Prod.ext rfl (Category.comp_id h).symm

private theorem shiftedTensorMap_comp_right
    {X Y U V W : ShiftedDerivedCategory R} (f : X ⟶ Y) (g : U ⟶ V) (h : V ⟶ W) :
    T.tensor.map (Prod.mkHom f (g ≫ h)) =
      T.tensor.map (Prod.mkHom f g) ≫ T.tensor.map (Prod.mkHom (𝟙 Y) h) := by
  rw [← T.tensor.map_comp]
  congr 1
  exact Prod.ext (Category.comp_id f).symm rfl

private theorem shiftedTensor_associativity_of_coherence (a b c : ℤ)
    (hc : ∀ K L M : ShiftedDerivedCategory R,
      (derivedTensorAssociator R T).hom.app ((K⟦a⟧, L⟦b⟧), M⟦c⟧) ≫
        T.tensor.map (Prod.mkHom (𝟙 (K⟦a⟧))
          ((shiftedTensorCanonicalComparison R T b c).hom.app (L, M))) ≫
        (shiftedTensorCanonicalComparison R T a (b + c)).hom.app
          (K, T.tensor.obj (L, M)) =
      T.tensor.map (Prod.mkHom
          ((shiftedTensorCanonicalComparison R T a b).hom.app (K, L)) (𝟙 (M⟦c⟧))) ≫
        (shiftedTensorCanonicalComparison R T (a + b) c).hom.app
          (T.tensor.obj (K, L), M) ≫
        (shiftFunctor _ ((a + b) + c)).map
          ((derivedTensorAssociator R T).hom.app ((K, L), M)) ≫
        (eqToIso (congrArg
          (fun n : ℤ ↦ (T.tensor.obj (K, T.tensor.obj (L, M)))⟦n⟧)
          (add_assoc a b c))).hom) :
    ShiftedTensorAssociativityClause R T a b c := by
  intro P Q S hP hQ hS K L M f g h
  have hn := (derivedTensorAssociator R T).hom.naturality
    (Prod.mkHom (Prod.mkHom f g) h)
  change T.tensor.map (Prod.mkHom (T.tensor.map (Prod.mkHom f g)) h) ≫
      (derivedTensorAssociator R T).hom.app ((K⟦a⟧, L⟦b⟧), M⟦c⟧) =
    (derivedTensorAssociator R T).hom.app
        ((shiftedDegreeZero R P, shiftedDegreeZero R Q), shiftedDegreeZero R S) ≫
      T.tensor.map (Prod.mkHom f (T.tensor.map (Prod.mkHom g h))) at hn
  simp only [shiftedTensorB, shiftedTensorMap_comp_left, shiftedTensorMap_comp_right,
    Category.assoc]
  rw [← reassoc_of% hn, hc]

private theorem shiftedTensor_symmetry_of_coherence (a b : ℤ)
    (hc : ∀ K L : ShiftedDerivedCategory R,
      (shiftedTensorCanonicalComparison R T a b).hom.app (K, L) ≫
        (shiftFunctor _ (a + b)).map ((derivedTensorSymmetry R T).hom.app (K, L)) =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        ((derivedTensorSymmetry R T).hom.app (K⟦a⟧, L⟦b⟧) ≫
          (shiftedTensorCanonicalComparison R T b a).hom.app (L, K) ≫
          (eqToIso (congrArg (fun n : ℤ ↦ (T.tensor.obj (L, K))⟦n⟧)
            (add_comm b a))).hom)) :
    ShiftedTensorSymmetryClause R T a b := by
  intro P Q hP hQ K L f g
  have hn := (derivedTensorSymmetry R T).hom.naturality (Prod.mkHom f g)
  change T.tensor.map (Prod.mkHom f g) ≫
      (derivedTensorSymmetry R T).hom.app (K⟦a⟧, L⟦b⟧) =
    (derivedTensorSymmetry R T).hom.app (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
      T.tensor.map (Prod.mkHom g f) at hn
  simp only [shiftedTensorB, Category.assoc]
  rw [hc, Preadditive.comp_zsmul, ← Category.assoc, hn]
  simp only [Category.assoc]

private theorem shiftedTensorModel_additive :
    ∀ X : ShiftedDerivedCategory R,
      ((Functor.curry.obj T.tensor).obj X).Additive ∧
      ((Functor.curry.obj T.tensor).flip.obj X).Additive := by
  obtain ⟨U, hU⟩ := shiftedTensorPublishedModel_exists R
  obtain ⟨e, _⟩ := DerivedTensorConstraints.extendBinary R U.tensor T.tensor
    (U.representative.symm ≪≫ T.representative)
  intro X
  obtain ⟨hL, hR, _⟩ := DerivedTensorConstraints.derived_tensor_additive R X
  let e' : KFlatFixedTensor.derivedTensor R ≅ Functor.curry.obj T.tensor :=
    (eqToIso (KFlatFixedTensor.derivedTensor_eq_published R)) ≪≫
      Functor.curry.mapIso ((eqToIso hU).symm ≪≫ e)
  constructor
  · exact Functor.additive_of_iso (e'.app X)
  · let ei : (KFlatFixedTensor.derivedTensor R).flip.obj X ≅
        (Functor.curry.obj T.tensor).flip.obj X :=
      ((flipFunctor _ _ _).mapIso e').app X
    exact Functor.additive_of_iso ei

private theorem shiftedTensorB_additivity (a b : ℤ) :
    ShiftedTensorAdditivityClause R T a b := by
  intro P Q hP hQ K L f₁ f₂ g₁ g₂
  have := (shiftedTensorModel_additive R T (shiftedDegreeZero R Q)).2
  have := (shiftedTensorModel_additive R T (K⟦a⟧)).1
  have hm {X X' Y Y' : ShiftedDerivedCategory R} (f : X ⟶ X') (g : Y ⟶ Y') :
      T.tensor.map (Prod.mkHom f g) =
        T.tensor.map (Prod.mkHom f (𝟙 Y)) ≫ T.tensor.map (Prod.mkHom (𝟙 X') g) := by
    rw [← T.tensor.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id f).symm (Category.id_comp g).symm
  have hL : T.tensor.map (Prod.mkHom (f₁ + f₂) (𝟙 (shiftedDegreeZero R Q))) =
      T.tensor.map (Prod.mkHom f₁ (𝟙 (shiftedDegreeZero R Q))) +
        T.tensor.map (Prod.mkHom f₂ (𝟙 (shiftedDegreeZero R Q))) :=
    Functor.map_add ((Functor.curry.obj T.tensor).flip.obj (shiftedDegreeZero R Q))
  have hR : T.tensor.map (Prod.mkHom (𝟙 (K⟦a⟧)) (g₁ + g₂)) =
      T.tensor.map (Prod.mkHom (𝟙 (K⟦a⟧)) g₁) +
        T.tensor.map (Prod.mkHom (𝟙 (K⟦a⟧)) g₂) :=
    Functor.map_add ((Functor.curry.obj T.tensor).obj (K⟦a⟧))
  constructor
  · simp only [shiftedTensorB]
    rw [hm (f₁ + f₂) g₁, hm f₁ g₁, hm f₂ g₁, hL,
      Preadditive.add_comp, Preadditive.add_comp]
  · simp only [shiftedTensorB]
    rw [hm f₁ (g₁ + g₂), hm f₁ g₁, hm f₁ g₂, hR,
      Preadditive.comp_add, Preadditive.add_comp]

private abbrev totalModel (E F : (shiftedTensorResolving R).FullSubcategory) :
    (shiftedTensorResolving R).FullSubcategory :=
  ⟨(shiftedTotalTensor R).obj (E.obj, F.obj),
    (DerivedTensorConstraints.derived_tensor_model_closure R).1 E F⟩

private def leftModelRepresentative
    (E F G : (shiftedTensorResolving R).FullSubcategory) :
    DerivedCategory.Q.obj ((shiftedTotalTensor R).obj ((totalModel R E F).obj, G.obj)) ⟶
      T.tensor.obj (T.tensor.obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) :=
  T.representative.hom.app (totalModel R E F, G) ≫
    T.tensor.map (Prod.mkHom (T.representative.hom.app (E, F)) (𝟙 _))

private def rightModelRepresentative
    (E F G : (shiftedTensorResolving R).FullSubcategory) :
    DerivedCategory.Q.obj ((shiftedTotalTensor R).obj (E.obj, (totalModel R F G).obj)) ⟶
      T.tensor.obj (DerivedCategory.Q.obj E.obj,
        T.tensor.obj (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)) :=
  T.representative.hom.app (E, totalModel R F G) ≫
    T.tensor.map (Prod.mkHom (𝟙 _) (T.representative.hom.app (F, G)))

private theorem swap_native (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    shiftedComplexSwap R E F =
      (letI := monoidalCategory R
       letI := symmetricCategory R
       letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
       CochainComplex.Monoidal.braiding E F) := by
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  apply shiftedComplexSwap_unique R E F _ _ (shiftedComplexSwap_signed R E F)
  intro p q
  erw [CochainComplex.Monoidal.ι_braiding_hom]
  change ((p * q).negOnePow : ℤ) • _ = _
  rw [show ((p * q).negOnePow : ℤ) = (-1 : ℤ) ^ (p * q).natAbs from
    Int.coe_negOnePow ℤ (p * q)]

private theorem pair_native (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (a b : ℤ) :
    (shiftedTensorComplexComparisonNatIso R a b).app (E, F) =
      (letI := monoidalCategory R
       letI := symmetricCategory R
       letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
       CategoryTheory.RingedDerivedNative.totalTensorShiftIso E F a b) := by
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  apply Iso.ext
  simp only [shiftedTensorComplexComparisonNatIso, totalTensorPairShift, tensorPairShift,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, tensorRightShift, tensorLeftShift,
    NatIso.ofComponents_hom_app, CategoryTheory.RingedDerivedNative.totalTensorShiftIso,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.commShiftIso_map₂CochainComplex_hom_app,
    Functor.commShiftIso_map₂CochainComplex_flip_hom_app]
  rfl

private theorem symmetry_normalization
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F) :
    T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩) ≫
        (derivedTensorSymmetry R T).hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) =
      DerivedCategory.Q.map (shiftedComplexSwap R E F).hom ≫
        T.representative.hom.app (⟨F, hF⟩, ⟨E, hE⟩) := by
  have hs : IsCanonicalDerivedTensorSymmetry R T (derivedTensorSymmetry R T) := by
    unfold derivedTensorSymmetry
    exact (derivedTensorSymmetry_exists R T).exists.choose_spec
  obtain ⟨χ, hχ, h⟩ := hs E F hE hF
  rw [shiftedComplexSwap_unique R E F χ (shiftedComplexSwap R E F)
    hχ (shiftedComplexSwap_signed R E F)] at h
  exact h

private theorem chain_symmetry
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (a b : ℤ) :
    (shiftedTensorComplexComparisonNatIso R a b).hom.app (E, F) ≫
        (shiftFunctor _ (a + b)).map (shiftedComplexSwap R E F).hom =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        ((shiftedComplexSwap R (E⟦a⟧) (F⟦b⟧)).hom ≫
          (shiftedTensorComplexComparisonNatIso R b a).hom.app (F, E) ≫
          (eqToIso (congrArg (fun n : ℤ ↦ ((shiftedTotalTensor R).obj (F, E))⟦n⟧)
            (add_comm b a))).hom) := by
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  have h := CategoryTheory.RingedDerivedNative.symmetryCoherence E F a b
  rw [← Iso.app_hom, pair_native R E F a b, ← Iso.app_hom, pair_native R F E b a]
  rw [swap_native R E F, swap_native R (E⟦a⟧) (F⟦b⟧)]
  have hsign : ((a * b).negOnePow : ℤ) = (-1 : ℤ) ^ (a * b).natAbs :=
    Int.coe_negOnePow ℤ (a * b)
  have hb (X Y : CochainComplex (ShiftedModuleCategory R) ℤ) :
      (β_ X Y) = CochainComplex.Monoidal.braiding X Y := by rfl
  simp only [hb] at h
  have ho (X Y : CochainComplex (ShiftedModuleCategory R) ℤ) :
      (shiftedTotalTensor R).obj (X, Y) = X ⊗ Y := by rfl
  simpa only [Functor.comp_obj, Functor.prod_obj, ho, Units.smul_def, hsign] using h

private theorem total_map
    {E E' F F' : CochainComplex (ShiftedModuleCategory R) ℤ} (f : E ⟶ E') (g : F ⟶ F') :
    (shiftedTotalTensor R).map (Prod.mkHom f g) =
      (letI := monoidalCategory R
       HomologicalComplex.tensorHom f g) := by
  letI := monoidalCategory R
  simp [shiftedTotalTensor, Functor.map₂HomologicalComplex, Functor.uncurry_obj_map,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  rfl

private theorem associator_formula (E F G : CochainComplex (ShiftedModuleCategory R) ℤ) :
    IsComplexTensorAssociator R E F G
      (letI := monoidalCategory R
       letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
       HomologicalComplex.associator E F G) := by
  letI := monoidalCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  intro p q r
  exact (CategoryTheory.RingedDerivedNative.associatorFormula E F G)
    p q r (p + q) (q + r) (p + q + r) rfl rfl rfl (add_assoc p q r).symm

private theorem associator_unique (E F G : CochainComplex (ShiftedModuleCategory R) ℤ)
    (χ χ' : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅
      (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G)))
    (hχ : IsComplexTensorAssociator R E F G χ)
    (hχ' : IsComplexTensorAssociator R E F G χ') : χ = χ' := by
  letI := monoidalCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
    (F₁₂ := curriedTensor (ShiftedModuleCategory R)) (G := curriedTensor (ShiftedModuleCategory R))
    (K₁ := E) (K₂ := F) (K₃ := G) (c₁₂ := .up ℤ) (c₄ := .up ℤ)
  intro p q r hn
  change p + q + r = n at hn
  subst n
  erw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor (ShiftedModuleCategory R))
    (curriedTensor (ShiftedModuleCategory R)) E F G (.up ℤ) (.up ℤ)
    p q r (p + q) ((p + q) + r) rfl rfl]
  simp only [Category.assoc]
  exact (hχ p q r).trans (hχ' p q r).symm

private theorem associator_normalization
    (E F G : (shiftedTensorResolving R).FullSubcategory) :
    leftModelRepresentative R T E F G ≫
        (derivedTensorAssociator R T).hom.app
          ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
            DerivedCategory.Q.obj G.obj) =
      DerivedCategory.Q.map
        (letI := monoidalCategory R
         letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
         (HomologicalComplex.associator E.obj F.obj G.obj).hom) ≫
        rightModelRepresentative R T E F G := by
  have hs : IsCanonicalTensorAssociator R T (derivedTensorAssociator R T) := by
    unfold derivedTensorAssociator
    exact (derivedTensorAssociator_exists R T).exists.choose_spec
  obtain ⟨hEF, hFG, χ, hχ, h⟩ := hs E.obj F.obj G.obj E.property F.property G.property
  rw [associator_unique R E.obj F.obj G.obj χ _ hχ
    (associator_formula R E.obj F.obj G.obj)] at h
  with_unfolding_all
    simpa only [leftModelRepresentative, rightModelRepresentative, totalModel,
      Functor.comp_obj, Functor.prod_obj, CategoryTheory.Functor.id_obj,
      CategoryTheory.prod.associator_obj, ObjectProperty.ι_obj, Category.assoc] using h

private theorem chain_associativity
    (E F G : CochainComplex (ShiftedModuleCategory R) ℤ) (a b c : ℤ) :
    (shiftedTotalTensor R).map (Prod.mkHom
        ((shiftedTensorComplexComparisonNatIso R a b).hom.app (E, F)) (𝟙 (G⟦c⟧))) ≫
      (shiftedTensorComplexComparisonNatIso R (a + b) c).hom.app
        ((shiftedTotalTensor R).obj (E, F), G) ≫
      (shiftFunctor _ ((a + b) + c)).map
        (letI := monoidalCategory R
         letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
         (HomologicalComplex.associator E F G).hom) =
    (letI := monoidalCategory R
     letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
     (HomologicalComplex.associator (E⟦a⟧) (F⟦b⟧) (G⟦c⟧)).hom) ≫
      (shiftedTotalTensor R).map (Prod.mkHom (𝟙 (E⟦a⟧))
        ((shiftedTensorComplexComparisonNatIso R b c).hom.app (F, G))) ≫
      (shiftedTensorComplexComparisonNatIso R a (b + c)).hom.app
        (E, (shiftedTotalTensor R).obj (F, G)) ≫
      (eqToIso (congrArg
        (fun n : ℤ ↦ ((shiftedTotalTensor R).obj
          (E, (shiftedTotalTensor R).obj (F, G)))⟦n⟧)
        (add_assoc a b c).symm)).hom := by
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  have h := CategoryTheory.RingedDerivedNative.associativityCoherence E F G a b c
  have ha (X Y Z : CochainComplex (ShiftedModuleCategory R) ℤ) :
      (α_ X Y Z) = HomologicalComplex.associator X Y Z := by rfl
  have hl {X Y Z : CochainComplex (ShiftedModuleCategory R) ℤ} (f : X ⟶ Y) :
      f ▷ Z = HomologicalComplex.tensorHom f (𝟙 Z) := by rfl
  have hr {X Y Z : CochainComplex (ShiftedModuleCategory R) ℤ} (g : Y ⟶ Z) :
      X ◁ g = HomologicalComplex.tensorHom (𝟙 X) g := by rfl
  simp only [ha, hl, hr] at h
  have ho (X Y : CochainComplex (ShiftedModuleCategory R) ℤ) :
      (shiftedTotalTensor R).obj (X, Y) = X ⊗ Y := by rfl
  simp only [Functor.comp_obj, Functor.prod_obj, total_map, ← Iso.app_hom,
    pair_native, ho]
  exact h

private theorem shift_normalization (a b : ℤ)
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
    (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F)
    (hEa : shiftedTensorResolving R (E⟦a⟧)) (hFb : shiftedTensorResolving R (F⟦b⟧)) :
    T.representative.hom.app (⟨E⟦a⟧, hEa⟩, ⟨F⟦b⟧, hFb⟩) ≫
        T.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).hom.app E)
          ((DerivedCategory.Q.commShiftIso b).hom.app F)) ≫
        (shiftedTensorCanonicalComparison R T a b).hom.app
          (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) =
      DerivedCategory.Q.map ((shiftedTensorComplexComparisonNatIso R a b).hom.app (E, F)) ≫
        (DerivedCategory.Q.commShiftIso (a + b)).hom.app _ ≫
        (shiftFunctor _ (a + b)).map (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) := by
  have hs : IsCanonicalShiftComparison R T a b (shiftedTensorCanonicalComparison R T a b) := by
    unfold shiftedTensorCanonicalComparison
    exact (shiftedTensorCanonicalComparison_exists R T a b).exists.choose_spec
  obtain ⟨_, _, h⟩ := hs E F hE hF
  exact h

private theorem leftShift_normalization (a b c : ℤ)
    (E F G : (shiftedTensorResolving R).FullSubcategory) :
    let Ea : (shiftedTensorResolving R).FullSubcategory :=
      ⟨E.obj⟦a⟧, shiftedModelShift_closed R E a⟩
    let Fb : (shiftedTensorResolving R).FullSubcategory :=
      ⟨F.obj⟦b⟧, shiftedModelShift_closed R F b⟩
    let Gc : (shiftedTensorResolving R).FullSubcategory :=
      ⟨G.obj⟦c⟧, shiftedModelShift_closed R G c⟩
    leftModelRepresentative R T Ea Fb Gc ≫
        T.tensor.map (Prod.mkHom
          (T.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).hom.app E.obj)
            ((DerivedCategory.Q.commShiftIso b).hom.app F.obj)))
          ((DerivedCategory.Q.commShiftIso c).hom.app G.obj)) ≫
        T.tensor.map (Prod.mkHom ((shiftedTensorCanonicalComparison R T a b).hom.app
          (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj))
          (𝟙 ((DerivedCategory.Q.obj G.obj)⟦c⟧))) ≫
        (shiftedTensorCanonicalComparison R T (a + b) c).hom.app
          (T.tensor.obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
            DerivedCategory.Q.obj G.obj) =
      DerivedCategory.Q.map
          ((shiftedTotalTensor R).map (Prod.mkHom
            ((shiftedTensorComplexComparisonNatIso R a b).hom.app (E.obj, F.obj))
            (𝟙 Gc.obj))) ≫
        DerivedCategory.Q.map
          ((shiftedTensorComplexComparisonNatIso R (a + b) c).hom.app
            ((totalModel R E F).obj, G.obj)) ≫
        (DerivedCategory.Q.commShiftIso ((a + b) + c)).hom.app _ ≫
        (shiftFunctor _ ((a + b) + c)).map (leftModelRepresentative R T E F G) := by
  dsimp only
  let q : CochainComplex (ShiftedModuleCategory R) ℤ ⥤ ShiftedDerivedCategory R :=
    DerivedCategory.Q
  let Ea : (shiftedTensorResolving R).FullSubcategory :=
    ⟨E.obj⟦a⟧, shiftedModelShift_closed R E a⟩
  let Fb : (shiftedTensorResolving R).FullSubcategory :=
    ⟨F.obj⟦b⟧, shiftedModelShift_closed R F b⟩
  let Gc : (shiftedTensorResolving R).FullSubcategory :=
    ⟨G.obj⟦c⟧, shiftedModelShift_closed R G c⟩
  let EF := totalModel R E F
  let EaFb := totalModel R Ea Fb
  let EFab : (shiftedTensorResolving R).FullSubcategory :=
    ⟨EF.obj⟦a + b⟧, shiftedModelShift_closed R EF (a + b)⟩
  let κE := (q.commShiftIso a).hom.app E.obj
  let κF := (q.commShiftIso b).hom.app F.obj
  let κG := (q.commShiftIso c).hom.app G.obj
  let κEF := (q.commShiftIso (a + b)).hom.app EF.obj
  let ρ : q.obj EF.obj ⟶ T.tensor.obj (q.obj E.obj, q.obj F.obj) :=
    T.representative.hom.app (E, F)
  let ρs : q.obj EaFb.obj ⟶ T.tensor.obj (q.obj Ea.obj, q.obj Fb.obj) :=
    T.representative.hom.app (Ea, Fb)
  let cEF := (shiftedTensorComplexComparisonNatIso R a b).hom.app (E.obj, F.obj)
  let tEF := (shiftedTensorCanonicalComparison R T a b).hom.app (q.obj E.obj, q.obj F.obj)
  let tOut := (shiftedTensorCanonicalComparison R T (a + b) c).hom.app
    (T.tensor.obj (q.obj E.obj, q.obj F.obj), q.obj G.obj)
  let tOut' := (shiftedTensorCanonicalComparison R T (a + b) c).hom.app
    (q.obj EF.obj, q.obj G.obj)
  have hInner : ρs ≫ T.tensor.map (Prod.mkHom κE κF) ≫ tEF =
      q.map cEF ≫ κEF ≫ (shiftFunctor _ (a + b)).map ρ :=
    shift_normalization R T a b E.obj F.obj E.property F.property Ea.property Fb.property
  have hFactor :
      T.tensor.map (Prod.mkHom ρs (𝟙 (q.obj Gc.obj))) ≫
        T.tensor.map (Prod.mkHom (T.tensor.map (Prod.mkHom κE κF)) κG) ≫
        T.tensor.map (Prod.mkHom tEF (𝟙 ((q.obj G.obj)⟦c⟧))) =
      T.tensor.map (Prod.mkHom (q.map cEF) (𝟙 (q.obj Gc.obj))) ≫
        T.tensor.map (Prod.mkHom κEF κG) ≫
        T.tensor.map (Prod.mkHom ((shiftFunctor _ (a + b)).map ρ)
          (𝟙 ((q.obj G.obj)⟦c⟧))) := by
    simp only [← T.tensor.map_comp, prod_comp, Category.assoc, Category.id_comp,
      Category.comp_id]
    congr 1
    exact Prod.ext hInner rfl
  have hNat := (shiftedTensorCanonicalComparison R T (a + b) c).hom.naturality
    (Prod.mkHom ρ (𝟙 (q.obj G.obj)))
  change T.tensor.map (Prod.mkHom ((shiftFunctor _ (a + b)).map ρ)
      ((shiftFunctor _ c).map (𝟙 (q.obj G.obj)))) ≫ tOut =
    tOut' ≫ (shiftFunctor _ ((a + b) + c)).map
      (T.tensor.map (Prod.mkHom ρ (𝟙 (q.obj G.obj)))) at hNat
  simp only [CategoryTheory.Functor.map_id] at hNat
  let fc : EaFb ⟶ EFab := ObjectProperty.homMk cEF
  have hRep := T.representative.hom.naturality (Prod.mkHom fc (𝟙 Gc))
  change q.map ((shiftedTotalTensor R).map (Prod.mkHom cEF (𝟙 Gc.obj))) ≫
      T.representative.hom.app (EFab, Gc) =
    T.representative.hom.app (EaFb, Gc) ≫
      T.tensor.map (Prod.mkHom (q.map cEF) (q.map (𝟙 Gc.obj))) at hRep
  have hRep' := hRep.trans (congrArg
    (fun z ↦ T.representative.hom.app (EaFb, Gc) ≫
      T.tensor.map (Prod.mkHom (q.map cEF) z)) (q.map_id Gc.obj))
  have hOuter := shift_normalization R T (a + b) c EF.obj G.obj
    EF.property G.property EFab.property Gc.property
  simp only [leftModelRepresentative, Category.assoc]
  change T.representative.hom.app (EaFb, Gc) ≫
      T.tensor.map (Prod.mkHom ρs (𝟙 (q.obj Gc.obj))) ≫
      T.tensor.map (Prod.mkHom (T.tensor.map (Prod.mkHom κE κF)) κG) ≫
      T.tensor.map (Prod.mkHom tEF (𝟙 ((q.obj G.obj)⟦c⟧))) ≫ tOut = _
  rw [reassoc_of% hFactor, hNat, ← reassoc_of% hRep', reassoc_of% hOuter]
  simp only [leftModelRepresentative, Functor.map_comp, Category.assoc]
  rfl

private theorem rightShift_normalization (a b c : ℤ)
    (E F G : (shiftedTensorResolving R).FullSubcategory) :
    let Ea : (shiftedTensorResolving R).FullSubcategory :=
      ⟨E.obj⟦a⟧, shiftedModelShift_closed R E a⟩
    let Fb : (shiftedTensorResolving R).FullSubcategory :=
      ⟨F.obj⟦b⟧, shiftedModelShift_closed R F b⟩
    let Gc : (shiftedTensorResolving R).FullSubcategory :=
      ⟨G.obj⟦c⟧, shiftedModelShift_closed R G c⟩
    rightModelRepresentative R T Ea Fb Gc ≫
        T.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).hom.app E.obj)
          (T.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso b).hom.app F.obj)
            ((DerivedCategory.Q.commShiftIso c).hom.app G.obj)))) ≫
        T.tensor.map (Prod.mkHom (𝟙 ((DerivedCategory.Q.obj E.obj)⟦a⟧))
          ((shiftedTensorCanonicalComparison R T b c).hom.app
            (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj))) ≫
        (shiftedTensorCanonicalComparison R T a (b + c)).hom.app
          (DerivedCategory.Q.obj E.obj,
            T.tensor.obj (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)) =
      DerivedCategory.Q.map
          ((shiftedTotalTensor R).map (Prod.mkHom (𝟙 Ea.obj)
            ((shiftedTensorComplexComparisonNatIso R b c).hom.app (F.obj, G.obj)))) ≫
        DerivedCategory.Q.map
          ((shiftedTensorComplexComparisonNatIso R a (b + c)).hom.app
            (E.obj, (totalModel R F G).obj)) ≫
        (DerivedCategory.Q.commShiftIso (a + (b + c))).hom.app _ ≫
        (shiftFunctor _ (a + (b + c))).map (rightModelRepresentative R T E F G) := by
  dsimp only
  let q : CochainComplex (ShiftedModuleCategory R) ℤ ⥤ ShiftedDerivedCategory R :=
    DerivedCategory.Q
  let Ea : (shiftedTensorResolving R).FullSubcategory :=
    ⟨E.obj⟦a⟧, shiftedModelShift_closed R E a⟩
  let Fb : (shiftedTensorResolving R).FullSubcategory :=
    ⟨F.obj⟦b⟧, shiftedModelShift_closed R F b⟩
  let Gc : (shiftedTensorResolving R).FullSubcategory :=
    ⟨G.obj⟦c⟧, shiftedModelShift_closed R G c⟩
  let FG := totalModel R F G
  let FbGc := totalModel R Fb Gc
  let FGbc : (shiftedTensorResolving R).FullSubcategory :=
    ⟨FG.obj⟦b + c⟧, shiftedModelShift_closed R FG (b + c)⟩
  let κE := (q.commShiftIso a).hom.app E.obj
  let κF := (q.commShiftIso b).hom.app F.obj
  let κG := (q.commShiftIso c).hom.app G.obj
  let κFG := (q.commShiftIso (b + c)).hom.app FG.obj
  let ρ : q.obj FG.obj ⟶ T.tensor.obj (q.obj F.obj, q.obj G.obj) :=
    T.representative.hom.app (F, G)
  let ρs : q.obj FbGc.obj ⟶ T.tensor.obj (q.obj Fb.obj, q.obj Gc.obj) :=
    T.representative.hom.app (Fb, Gc)
  let cFG := (shiftedTensorComplexComparisonNatIso R b c).hom.app (F.obj, G.obj)
  let tFG := (shiftedTensorCanonicalComparison R T b c).hom.app (q.obj F.obj, q.obj G.obj)
  let tOut := (shiftedTensorCanonicalComparison R T a (b + c)).hom.app
    (q.obj E.obj, T.tensor.obj (q.obj F.obj, q.obj G.obj))
  let tOut' := (shiftedTensorCanonicalComparison R T a (b + c)).hom.app
    (q.obj E.obj, q.obj FG.obj)
  have hInner : ρs ≫ T.tensor.map (Prod.mkHom κF κG) ≫ tFG =
      q.map cFG ≫ κFG ≫ (shiftFunctor _ (b + c)).map ρ :=
    shift_normalization R T b c F.obj G.obj F.property G.property Fb.property Gc.property
  have hFactor :
      T.tensor.map (Prod.mkHom (𝟙 (q.obj Ea.obj)) ρs) ≫
        T.tensor.map (Prod.mkHom κE (T.tensor.map (Prod.mkHom κF κG))) ≫
        T.tensor.map (Prod.mkHom (𝟙 ((q.obj E.obj)⟦a⟧)) tFG) =
      T.tensor.map (Prod.mkHom (𝟙 (q.obj Ea.obj)) (q.map cFG)) ≫
        T.tensor.map (Prod.mkHom κE κFG) ≫
        T.tensor.map (Prod.mkHom (𝟙 ((q.obj E.obj)⟦a⟧))
          ((shiftFunctor _ (b + c)).map ρ)) := by
    simp only [← T.tensor.map_comp, prod_comp, Category.assoc, Category.id_comp,
      Category.comp_id]
    congr 1
    exact Prod.ext rfl hInner
  have hNat := (shiftedTensorCanonicalComparison R T a (b + c)).hom.naturality
    (Prod.mkHom (𝟙 (q.obj E.obj)) ρ)
  change T.tensor.map (Prod.mkHom ((shiftFunctor _ a).map (𝟙 (q.obj E.obj)))
      ((shiftFunctor _ (b + c)).map ρ)) ≫ tOut =
    tOut' ≫ (shiftFunctor _ (a + (b + c))).map
      (T.tensor.map (Prod.mkHom (𝟙 (q.obj E.obj)) ρ)) at hNat
  simp only [CategoryTheory.Functor.map_id] at hNat
  let fc : FbGc ⟶ FGbc := ObjectProperty.homMk cFG
  have hRep := T.representative.hom.naturality (Prod.mkHom (𝟙 Ea) fc)
  change q.map ((shiftedTotalTensor R).map (Prod.mkHom (𝟙 Ea.obj) cFG)) ≫
      T.representative.hom.app (Ea, FGbc) =
    T.representative.hom.app (Ea, FbGc) ≫
      T.tensor.map (Prod.mkHom (q.map (𝟙 Ea.obj)) (q.map cFG)) at hRep
  have hRep' := hRep.trans (congrArg
    (fun z ↦ T.representative.hom.app (Ea, FbGc) ≫
      T.tensor.map (Prod.mkHom z (q.map cFG))) (q.map_id Ea.obj))
  have hOuter := shift_normalization R T a (b + c) E.obj FG.obj
    E.property FG.property Ea.property FGbc.property
  simp only [rightModelRepresentative, Category.assoc]
  change T.representative.hom.app (Ea, FbGc) ≫
      T.tensor.map (Prod.mkHom (𝟙 (q.obj Ea.obj)) ρs) ≫
      T.tensor.map (Prod.mkHom κE (T.tensor.map (Prod.mkHom κF κG))) ≫
      T.tensor.map (Prod.mkHom (𝟙 ((q.obj E.obj)⟦a⟧)) tFG) ≫ tOut = _
  rw [reassoc_of% hFactor, hNat, ← reassoc_of% hRep', reassoc_of% hOuter]
  simp only [rightModelRepresentative, Functor.map_comp, Category.assoc]
  rfl

private theorem shifted_symmetry_on_models (a b : ℤ)
    (E F : (shiftedTensorResolving R).FullSubcategory) :
    (shiftedTensorCanonicalComparison R T a b).hom.app
        (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≫
        (shiftFunctor _ (a + b)).map ((derivedTensorSymmetry R T).hom.app
          (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj)) =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        ((derivedTensorSymmetry R T).hom.app
            ((DerivedCategory.Q.obj E.obj)⟦a⟧, (DerivedCategory.Q.obj F.obj)⟦b⟧) ≫
          (shiftedTensorCanonicalComparison R T b a).hom.app
            (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj E.obj) ≫
          (eqToIso (congrArg
            (fun n : ℤ ↦ (T.tensor.obj (DerivedCategory.Q.obj F.obj,
              DerivedCategory.Q.obj E.obj))⟦n⟧) (add_comm b a))).hom) := by
  let q : CochainComplex (ShiftedModuleCategory R) ℤ ⥤ ShiftedDerivedCategory R :=
    DerivedCategory.Q
  let Ea : (shiftedTensorResolving R).FullSubcategory :=
    ⟨E.obj⟦a⟧, shiftedModelShift_closed R E a⟩
  let Fb : (shiftedTensorResolving R).FullSubcategory :=
    ⟨F.obj⟦b⟧, shiftedModelShift_closed R F b⟩
  let eE := (q.commShiftIso a).app E.obj
  let eF := (q.commShiftIso b).app F.obj
  let r := T.representative.hom.app (Ea, Fb) ≫
    T.tensor.map (Prod.mkHom eE.hom eF.hom)
  let r' := T.representative.hom.app (Fb, Ea) ≫
    T.tensor.map (Prod.mkHom eF.hom eE.hom)
  let s := T.representative.hom.app (E, F)
  let s' := T.representative.hom.app (F, E)
  let c := q.map ((shiftedTensorComplexComparisonNatIso R a b).hom.app (E.obj, F.obj)) ≫
    (q.commShiftIso (a + b)).hom.app _
  let c' := q.map ((shiftedTensorComplexComparisonNatIso R b a).hom.app (F.obj, E.obj)) ≫
    (q.commShiftIso (b + a)).hom.app _
  let χ := q.map (shiftedComplexSwap R Ea.obj Fb.obj).hom
  let ψ := q.map (shiftedComplexSwap R E.obj F.obj).hom
  have hi : IsIso (Prod.mkHom eE.hom eF.hom) := (Iso.prod eE eF).isIso_hom
  have : IsIso r := by dsimp only [r]; infer_instance
  have ht := shift_normalization R T a b E.obj F.obj E.property F.property
    Ea.property Fb.property
  have ht' := shift_normalization R T b a F.obj E.obj F.property E.property
    Fb.property Ea.property
  have hs := symmetry_normalization R T E.obj F.obj E.property F.property
  have hs' : r ≫ (derivedTensorSymmetry R T).hom.app
      ((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧) = χ ≫ r' := by
    have hn := (derivedTensorSymmetry R T).hom.naturality (Prod.mkHom eE.hom eF.hom)
    change T.tensor.map (Prod.mkHom eE.hom eF.hom) ≫
        (derivedTensorSymmetry R T).hom.app
          ((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧) =
      (derivedTensorSymmetry R T).hom.app (q.obj Ea.obj, q.obj Fb.obj) ≫
        T.tensor.map (Prod.mkHom eF.hom eE.hom) at hn
    dsimp only [r, r', χ]
    rw [Category.assoc, hn, ← Category.assoc,
      symmetry_normalization R T Ea.obj Fb.obj Ea.property Fb.property, Category.assoc]
  have hc : c ≫ (shiftFunctor _ (a + b)).map ψ =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        (χ ≫ c' ≫ eqToHom (congrArg
          (fun n : ℤ ↦ (q.obj ((shiftedTotalTensor R).obj (F.obj, E.obj)))⟦n⟧)
          (add_comm b a))) := by
    have h := congrArg (fun z ↦ q.map z ≫
      (q.commShiftIso (a + b)).hom.app ((shiftedTotalTensor R).obj (F.obj, E.obj)))
      (chain_symmetry R E.obj F.obj a b)
    simp only [Functor.map_comp, Functor.map_zsmul, Preadditive.zsmul_comp,
      Category.assoc] at h
    erw [(q.commShiftIso (a + b)).hom.naturality] at h
    erw [mapShiftEqToHom q ((shiftedTotalTensor R).obj (F.obj, E.obj))
      (b + a) (a + b) (add_comm b a)] at h
    simpa only [c, c', χ, ψ, Ea, Fb, q, Functor.comp_map, Category.assoc] using h
  exact symmetryDiagram (a + b) (b + a) (add_comm b a)
    ((-1 : ℤ) ^ Int.natAbs (a * b)) r r' s s'
    ((shiftedTensorCanonicalComparison R T a b).hom.app (q.obj E.obj, q.obj F.obj))
    ((shiftedTensorCanonicalComparison R T b a).hom.app (q.obj F.obj, q.obj E.obj))
    ((derivedTensorSymmetry R T).hom.app (q.obj E.obj, q.obj F.obj))
    ((derivedTensorSymmetry R T).hom.app ((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧))
    c c' χ ψ
    (by simpa only [r, c, s, eE, eF, Iso.app_hom, Category.assoc] using ht)
    (by simpa only [r', c', s', eE, eF, Iso.app_hom, Category.assoc] using ht')
    hs hs' hc

set_option maxHeartbeats 800000 in
-- The iterated tensor representatives need additional elaboration heartbeats.
private theorem shifted_associativity_on_models (a b c : ℤ)
    (E F G : (shiftedTensorResolving R).FullSubcategory) :
    (derivedTensorAssociator R T).hom.app
        (((DerivedCategory.Q.obj E.obj)⟦a⟧, (DerivedCategory.Q.obj F.obj)⟦b⟧),
          (DerivedCategory.Q.obj G.obj)⟦c⟧) ≫
      T.tensor.map (Prod.mkHom (𝟙 ((DerivedCategory.Q.obj E.obj)⟦a⟧))
        ((shiftedTensorCanonicalComparison R T b c).hom.app
          (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj))) ≫
      (shiftedTensorCanonicalComparison R T a (b + c)).hom.app
        (DerivedCategory.Q.obj E.obj,
          T.tensor.obj (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)) =
    T.tensor.map (Prod.mkHom ((shiftedTensorCanonicalComparison R T a b).hom.app
        (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj))
        (𝟙 ((DerivedCategory.Q.obj G.obj)⟦c⟧))) ≫
      (shiftedTensorCanonicalComparison R T (a + b) c).hom.app
        (T.tensor.obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
          DerivedCategory.Q.obj G.obj) ≫
      (shiftFunctor _ ((a + b) + c)).map ((derivedTensorAssociator R T).hom.app
        ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj), DerivedCategory.Q.obj G.obj)) ≫
      (eqToIso (congrArg
        (fun n : ℤ ↦ (T.tensor.obj (DerivedCategory.Q.obj E.obj,
          T.tensor.obj (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)))⟦n⟧)
        (add_assoc a b c))).hom := by
  letI := monoidalCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  let q : CochainComplex (ShiftedModuleCategory R) ℤ ⥤ ShiftedDerivedCategory R :=
    DerivedCategory.Q
  let Ea : (shiftedTensorResolving R).FullSubcategory :=
    ⟨E.obj⟦a⟧, shiftedModelShift_closed R E a⟩
  let Fb : (shiftedTensorResolving R).FullSubcategory :=
    ⟨F.obj⟦b⟧, shiftedModelShift_closed R F b⟩
  let Gc : (shiftedTensorResolving R).FullSubcategory :=
    ⟨G.obj⟦c⟧, shiftedModelShift_closed R G c⟩
  let eE := (q.commShiftIso a).app E.obj
  let eF := (q.commShiftIso b).app F.obj
  let eG := (q.commShiftIso c).app G.obj
  let eL := T.tensor.mapIso (Iso.prod (T.tensor.mapIso (Iso.prod eE eF)) eG)
  let eR := T.tensor.mapIso (Iso.prod eE (T.tensor.mapIso (Iso.prod eF eG)))
  let r := leftModelRepresentative R T Ea Fb Gc ≫ eL.hom
  let r' := rightModelRepresentative R T Ea Fb Gc ≫ eR.hom
  let s := leftModelRepresentative R T E F G
  let s' := rightModelRepresentative R T E F G
  let tL := T.tensor.map (Prod.mkHom
    ((shiftedTensorCanonicalComparison R T a b).hom.app (q.obj E.obj, q.obj F.obj))
    (𝟙 ((q.obj G.obj)⟦c⟧))) ≫
    (shiftedTensorCanonicalComparison R T (a + b) c).hom.app
      (T.tensor.obj (q.obj E.obj, q.obj F.obj), q.obj G.obj)
  let tR := T.tensor.map (Prod.mkHom (𝟙 ((q.obj E.obj)⟦a⟧))
    ((shiftedTensorCanonicalComparison R T b c).hom.app (q.obj F.obj, q.obj G.obj))) ≫
    (shiftedTensorCanonicalComparison R T a (b + c)).hom.app
      (q.obj E.obj, T.tensor.obj (q.obj F.obj, q.obj G.obj))
  let cL := q.map ((shiftedTotalTensor R).map (Prod.mkHom
    ((shiftedTensorComplexComparisonNatIso R a b).hom.app (E.obj, F.obj)) (𝟙 Gc.obj))) ≫
    q.map ((shiftedTensorComplexComparisonNatIso R (a + b) c).hom.app
      ((totalModel R E F).obj, G.obj)) ≫ (q.commShiftIso ((a + b) + c)).hom.app _
  let cR := q.map ((shiftedTotalTensor R).map (Prod.mkHom (𝟙 Ea.obj)
    ((shiftedTensorComplexComparisonNatIso R b c).hom.app (F.obj, G.obj)))) ≫
    q.map ((shiftedTensorComplexComparisonNatIso R a (b + c)).hom.app
      (E.obj, (totalModel R F G).obj)) ≫ (q.commShiftIso (a + (b + c))).hom.app _
  let χ := q.map (HomologicalComplex.associator Ea.obj Fb.obj Gc.obj).hom
  let ψ := q.map (HomologicalComplex.associator E.obj F.obj G.obj).hom
  have hl : IsIso (leftModelRepresentative R T Ea Fb Gc) := by
    change IsIso ((T.representative.app (totalModel R Ea Fb, Gc) ≪≫
      T.tensor.mapIso (Iso.prod (T.representative.app (Ea, Fb))
        (Iso.refl (q.obj Gc.obj)))).hom)
    infer_instance
  have : IsIso r := by dsimp only [r]; infer_instance
  have ht : r ≫ tL = cL ≫ (shiftFunctor _ ((a + b) + c)).map s := by
    simpa only [r, tL, cL, s, eL, eE, eF, eG, Ea, Fb, Gc,
      Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom, Category.assoc] using
      leftShift_normalization R T a b c E F G
  have ht' : r' ≫ tR = cR ≫ (shiftFunctor _ (a + (b + c))).map s' := by
    simpa only [r', tR, cR, s', eR, eE, eF, eG, Ea, Fb, Gc,
      Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom, Category.assoc] using
      rightShift_normalization R T a b c E F G
  have hs := associator_normalization R T E F G
  have hs' : r ≫ (derivedTensorAssociator R T).hom.app
      (((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧), (q.obj G.obj)⟦c⟧) = χ ≫ r' := by
    have hn := (derivedTensorAssociator R T).hom.naturality
      (Prod.mkHom (Prod.mkHom eE.hom eF.hom) eG.hom)
    change eL.hom ≫ (derivedTensorAssociator R T).hom.app
        (((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧), (q.obj G.obj)⟦c⟧) =
      (derivedTensorAssociator R T).hom.app ((q.obj Ea.obj, q.obj Fb.obj), q.obj Gc.obj) ≫
        eR.hom at hn
    dsimp only [r, r', χ]
    rw [Category.assoc, hn, ← Category.assoc,
      associator_normalization R T Ea Fb Gc, Category.assoc]
  have hc : cL ≫ (shiftFunctor _ ((a + b) + c)).map ψ =
      (1 : ℤ) • (χ ≫ cR ≫ eqToHom (congrArg
        (fun n : ℤ ↦ (q.obj ((shiftedTotalTensor R).obj
          (E.obj, (totalModel R F G).obj)))⟦n⟧) (add_assoc a b c).symm)) := by
    have h := congrArg (fun z ↦ q.map z ≫
      (q.commShiftIso ((a + b) + c)).hom.app
        ((shiftedTotalTensor R).obj (E.obj, (totalModel R F G).obj)))
      (chain_associativity R E.obj F.obj G.obj a b c)
    simp only [Functor.map_comp, Category.assoc] at h
    erw [(q.commShiftIso ((a + b) + c)).hom.naturality] at h
    erw [mapShiftEqToHom q ((shiftedTotalTensor R).obj (E.obj, (totalModel R F G).obj))
      (a + (b + c)) ((a + b) + c) (add_assoc a b c).symm] at h
    simpa only [cL, cR, χ, ψ, Ea, Fb, Gc, q, totalModel, one_smul,
      Functor.comp_map, Category.assoc] using h
  have hd := symmetryDiagram ((a + b) + c) (a + (b + c)) (add_assoc a b c).symm
    (1 : ℤ) r r' s s' tL tR
    ((derivedTensorAssociator R T).hom.app ((q.obj E.obj, q.obj F.obj), q.obj G.obj))
    ((derivedTensorAssociator R T).hom.app
      (((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧), (q.obj G.obj)⟦c⟧))
    cL cR χ ψ ht ht' hs hs' hc
  have h := congrArg (fun z ↦ z ≫ eqToHom (congrArg
    (fun n : ℤ ↦ (T.tensor.obj (q.obj E.obj,
      T.tensor.obj (q.obj F.obj, q.obj G.obj)))⟦n⟧) (add_assoc a b c))) hd
  simpa only [one_smul, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    tL, tR, q, eqToIso, Functor.comp_obj] using h.symm

private theorem shiftedTensor_associativity_coherence (a b c : ℤ) :
    ∀ K L M : ShiftedDerivedCategory R,
      (derivedTensorAssociator R T).hom.app ((K⟦a⟧, L⟦b⟧), M⟦c⟧) ≫
        T.tensor.map (Prod.mkHom (𝟙 (K⟦a⟧))
          ((shiftedTensorCanonicalComparison R T b c).hom.app (L, M))) ≫
        (shiftedTensorCanonicalComparison R T a (b + c)).hom.app
          (K, T.tensor.obj (L, M)) =
      T.tensor.map (Prod.mkHom
          ((shiftedTensorCanonicalComparison R T a b).hom.app (K, L)) (𝟙 (M⟦c⟧))) ≫
        (shiftedTensorCanonicalComparison R T (a + b) c).hom.app
          (T.tensor.obj (K, L), M) ≫
        (shiftFunctor _ ((a + b) + c)).map
          ((derivedTensorAssociator R T).hom.app ((K, L), M)) ≫
        (eqToIso (congrArg
          (fun n : ℤ ↦ (T.tensor.obj (K, T.tensor.obj (L, M)))⟦n⟧)
          (add_assoc a b c))).hom := by
  let D := ShiftedDerivedCategory R
  let S := ((shiftFunctor D a).prod (shiftFunctor D b)).prod (shiftFunctor D c)
  let A := CategoryTheory.prod.associator D D D
  let α := derivedTensorAssociator R T
  let l : S ⋙ shiftedTensorLeftTriple R T ≅
      shiftedTensorLeftTriple R T ⋙ shiftFunctor D ((a + b) + c) :=
    isoWhiskerRight (NatIso.prod (shiftedTensorCanonicalComparison R T a b)
      (Iso.refl (shiftFunctor D c))) T.tensor ≪≫
      isoWhiskerLeft (T.tensor.prod (𝟭 D)) (shiftedTensorCanonicalComparison R T (a + b) c)
  let r : S ⋙ shiftedTensorRightTriple R T ≅
      shiftedTensorRightTriple R T ⋙ shiftFunctor D (a + (b + c)) :=
    isoWhiskerLeft A
      (isoWhiskerRight (NatIso.prod (Iso.refl (shiftFunctor D a))
          (shiftedTensorCanonicalComparison R T b c)) T.tensor ≪≫
        isoWhiskerLeft ((𝟭 D).prod T.tensor)
          (shiftedTensorCanonicalComparison R T a (b + c)))
  let lhs : S ⋙ shiftedTensorLeftTriple R T ≅
      shiftedTensorRightTriple R T ⋙ shiftFunctor D (a + (b + c)) :=
    isoWhiskerLeft S α ≪≫ r
  let rhs : S ⋙ shiftedTensorLeftTriple R T ≅
      shiftedTensorRightTriple R T ⋙ shiftFunctor D (a + (b + c)) :=
    l ≪≫ isoWhiskerRight α (shiftFunctor D ((a + b) + c)) ≪≫
      isoWhiskerLeft (shiftedTensorRightTriple R T)
        (eqToIso (congrArg (shiftFunctor D) (add_assoc a b c)))
  have happ (X : D) (n m : ℤ) (h : n = m) :
      (eqToIso (congrArg (shiftFunctor D) h)).hom.app X =
        eqToHom (congrArg (fun k : ℤ ↦ X⟦k⟧) h) := by
    subst m
    rfl
  have h : lhs = rhs := by
    apply DerivedTensorConstraints.ternary_iso_ext R
    intro E F G
    apply Iso.ext
    simpa only [lhs, rhs, α, S, A, D, l, r, Iso.app_hom, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app,
      whiskerLeft_app, NatIso.prod_hom, NatTrans.prod, Functor.prod_obj, Functor.comp_obj,
      Functor.id_obj, CategoryTheory.prod.associator, Iso.refl_hom, NatTrans.id_app,
      happ, eqToIso, eqToHom_app, Category.assoc] using
      shifted_associativity_on_models R T a b c E F G
  intro K L M
  have h' := congrArg (fun e ↦ e.hom.app ((K, L), M)) h
  simpa only [lhs, rhs, α, S, A, D, l, r, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    NatIso.prod_hom, NatTrans.prod, Functor.prod_obj, Functor.comp_obj, Functor.id_obj,
    CategoryTheory.prod.associator, Iso.refl_hom, NatTrans.id_app, happ, eqToIso,
    eqToHom_app, Category.assoc] using h'

private theorem shiftedTensor_symmetry_coherence (a b : ℤ) :
    ∀ K L : ShiftedDerivedCategory R,
      (shiftedTensorCanonicalComparison R T a b).hom.app (K, L) ≫
        (shiftFunctor _ (a + b)).map ((derivedTensorSymmetry R T).hom.app (K, L)) =
      ((-1 : ℤ) ^ Int.natAbs (a * b)) •
        ((derivedTensorSymmetry R T).hom.app (K⟦a⟧, L⟦b⟧) ≫
          (shiftedTensorCanonicalComparison R T b a).hom.app (L, K) ≫
          (eqToIso (congrArg (fun n : ℤ ↦ (T.tensor.obj (L, K))⟦n⟧)
            (add_comm b a))).hom) := by
  let D := ShiftedDerivedCategory R
  let S := (shiftFunctor D a).prod (shiftFunctor D b)
  let swap := CategoryTheory.Prod.swap D D
  let σ := derivedTensorSymmetry R T
  let lhs : S ⋙ T.tensor ≅ swap ⋙ T.tensor ⋙ shiftFunctor D (a + b) :=
    shiftedTensorCanonicalComparison R T a b ≪≫
      isoWhiskerRight σ (shiftFunctor D (a + b))
  let rhs : S ⋙ T.tensor ≅ swap ⋙ T.tensor ⋙ shiftFunctor D (a + b) :=
    (a * b).negOnePow •
      (isoWhiskerLeft S σ ≪≫ isoWhiskerLeft swap
        (shiftedTensorCanonicalComparison R T b a) ≪≫
        isoWhiskerLeft (swap ⋙ T.tensor)
          (eqToIso (congrArg (shiftFunctor D) (add_comm b a))))
  have happ (X : D) (n m : ℤ) (h : n = m) :
      (eqToIso (congrArg (shiftFunctor D) h)).hom.app X =
        eqToHom (congrArg (fun k : ℤ ↦ X⟦k⟧) h) := by
    subst m
    rfl
  have hsign : ((a * b).negOnePow : ℤ) = (-1 : ℤ) ^ (a * b).natAbs :=
    Int.coe_negOnePow ℤ (a * b)
  have h : lhs = rhs := by
    apply DerivedTensorConstraints.binary_iso_ext R
    intro E F
    apply Iso.ext
    simpa only [lhs, rhs, σ, S, swap, D, Iso.app_hom, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app,
      whiskerLeft_app, Preadditive.smul_iso_hom, Units.smul_def, NatTrans.app_zsmul, hsign,
      happ, eqToIso, eqToHom_app, Functor.prod_obj, Functor.comp_obj,
      CategoryTheory.Prod.swap_obj, Category.assoc] using shifted_symmetry_on_models R T a b E F
  intro K L
  have h' := congrArg (fun e ↦ e.hom.app (K, L)) h
  simpa only [lhs, rhs, σ, S, swap, D, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Preadditive.smul_iso_hom, Units.smul_def, NatTrans.app_zsmul, hsign, happ, eqToIso,
    eqToHom_app, Functor.prod_obj,
    Functor.comp_obj, CategoryTheory.Prod.swap_obj, Category.assoc] using h'

private theorem mixedBinaryIso_ext
    {D : Type u₂} [Category.{v₂} D]
    {U V : ShiftedDerivedCategory R × ShiftedDerivedCategory R ⥤ D} (s t : U ≅ V)
    (h : ∀ E F : (shiftedTensorResolving R).FullSubcategory,
      s.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) =
        t.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj)) : s = t := by
  let L := DerivedTensorConstraints.localization R
  let W := (HomotopyCategory.quasiIso (ShiftedModuleCategory R) (.up ℤ)).inverseImage
    (DerivedTensorConstraints.resolvingHomotopy R).ι
  have : L.IsLocalization W := DerivedTensorConstraints.localization_isLocalization R
  apply Iso.ext
  apply Localization.natTrans_ext (L.prod L) (W.prod W)
  intro E
  simpa only [L, DerivedTensorConstraints.localization, Functor.prod_obj,
    Functor.comp_obj, ObjectProperty.ι_obj, DerivedCategory.Q, DerivedCategory.Qh,
      HomologicalComplexUpToQuasiIso.Qh,
    CategoryTheory.Quotient.lift, Iso.app_hom] using
    congrArg Iso.hom (h ⟨E.1.obj.as, E.1.property⟩ ⟨E.2.obj.as, E.2.property⟩)

private theorem mixedTernaryIso_ext
    {D : Type u₂} [Category.{v₂} D]
    {U V : (ShiftedDerivedCategory R × ShiftedDerivedCategory R) ×
        ShiftedDerivedCategory R ⥤ D} (s t : U ≅ V)
    (h : ∀ E F G : (shiftedTensorResolving R).FullSubcategory,
      s.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) =
      t.app ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj)) : s = t := by
  let L := DerivedTensorConstraints.localization R
  let W := (HomotopyCategory.quasiIso (ShiftedModuleCategory R) (.up ℤ)).inverseImage
    (DerivedTensorConstraints.resolvingHomotopy R).ι
  have : L.IsLocalization W := DerivedTensorConstraints.localization_isLocalization R
  apply Iso.ext
  apply Localization.natTrans_ext ((L.prod L).prod L) ((W.prod W).prod W)
  intro E
  simpa only [L, DerivedTensorConstraints.localization, Functor.prod_obj,
    Functor.comp_obj, ObjectProperty.ι_obj, DerivedCategory.Q, DerivedCategory.Qh,
      HomologicalComplexUpToQuasiIso.Qh,
    CategoryTheory.Quotient.lift, Iso.app_hom] using
    congrArg Iso.hom (h ⟨E.1.1.obj.as, E.1.1.property⟩
      ⟨E.1.2.obj.as, E.1.2.property⟩ ⟨E.2.obj.as, E.2.property⟩)


end SignedMorphismProofs

/-- The local signed calculus for flat sources and arbitrary derived targets.
Source: Stacks 0FPL/0FPM; all ten proof steps of the DAG node are retained below
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof plan:
1. On E[a]^p tensor F[b]^q, move the second shift first. Its sign is (-1)^(bp);
   the two differential coefficients agree as checked in the node's Step 1.
2. The unsigned associator respects the coefficients 1, (-1)^p, (-1)^(p+q).
   Tensor and shifts preserve K-flatness and flat terms, by tensoring an acyclic
   test complex twice and using flatness of sums and tensor products.
3. Descend these maps and the Koszul swap uniquely using
   lem-weil-pbc-site-derived-tensor-descent, variable by variable.
4. Ordinary additive tensor preserves biproduct diagrams; resolving comparisons
   descend this property. Bilinear composition proves both additivity equations.
5. Associativity signs are bp+c(p+q)=cq+(b+c)p. Descend and precompose with f,g,h.
6. Symmetry signs differ by 2bp: bp+(p+a)(q+b) and ab+pq+aq. Descend and use naturality.
7. Flat degree-zero sheaves are K-flat (lem-pc-kflat-closure). Their tensor is flat
   because tensoring by it is the composite of two exact tensor functors. Thus the
   iterated B operations have the specified flat degree-zero sources.
8. For pullback, use the algebraic inverse image and scalar extension in
   def-weil-pbc-algebraic-inverse-image and the pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison. Its associator and swap squares
   agree on locally generating pure tensors.
9. Module pullback preserves sums by lem-weil-pbc-ringed-topoi-module-adjunction.
   Sum the ordinary comparisons over bidegrees. Additivity preserves all differential,
   shift and swap signs; the unsigned associator is preserved by Step 8.
10. lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves resolving models.
   Its unique representative comparison descends the Step 9 diagrams. Exactness
   identifies its derived functor with termwise pullback. The degree-zero comparison
   identifies pulled-back f,g with maps out of uStar P,uStar Q, which are flat.
   Naturality of t gives the pullback clause, including all coherence squares. -/
theorem shiftedTensorMorphismCalculus_local (a b c : ℤ) :
    ShiftedTensorAdditivityClause R T a b ∧
    ShiftedTensorAssociativityClause R T a b c ∧
    ShiftedTensorSymmetryClause R T a b := by
  exact ⟨shiftedTensorB_additivity R T a b,
    shiftedTensor_associativity_of_coherence R T a b c
      (shiftedTensor_associativity_coherence R T a b c),
    shiftedTensor_symmetry_of_coherence R T a b
      (shiftedTensor_symmetry_coherence R T a b)⟩

section Pullback

open CanonicalTensorPullbackOfUniverses
open scoped ChangeOfRings

variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
  [J'.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J' AddCommGrpCat.{max u v}]
  (S RI : Sheaf J' CommRingCat.{max u v})
  [HasDerivedCategory.{w} (ShiftedModuleCategory S)]
  (TS : ShiftedTensorModel S)
  (uInv : Sheaf J (Type (max u v)) ⥤ Sheaf J' (Type (max u v)))
  (uPush : Sheaf J' (Type (max u v)) ⥤ Sheaf J (Type (max u v)))
  (adj : uInv ⊣ uPush) [hlex : PreservesFiniteLimits uInv]
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (uStar : ShiftedModuleCategory R ⥤ ShiftedModuleCategory S)
  (hobj : ∀ M : ShiftedModuleCategory R, uStar.obj M = changeOfRings c (I.modules.obj M))
  (hmap : ∀ {M N : ShiftedModuleCategory R} (f : M ⟶ N),
    uStar.map f = eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M)
      (I.modules.map f) ≫ eqToHom (hobj N).symm)
  [uStar.Additive] [PreservesFiniteLimits uStar] [PreservesFiniteColimits uStar]
  (V : ShiftedModuleCategory S ⥤ ShiftedModuleCategory R) (am : uStar ⊣ V)
  (k : CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison.{u, v}
    R S RI uInv I c uStar hobj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
include uPush adj hmap hlex in
/-- The exact pullback comparison is uniquely fixed by the total-complex comparison.
No arbitrary natural isomorphism is assumed. The square uses the canonical ordinary
pure-tensor comparison k and the actual termwise derived functor.
Source: Stacks 07A4/03EL (blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof (Steps 8--10): use the specified scalar-extension functor and its module adjunction.
The ordinary pure-tensor comparison gives k.totalIso. Exactness makes termwise pullback
invert every quasi-isomorphism. The normalized representative square in
ringedTopoiCanonicalDerivedTensorPullback then gives this comparison; tensor descent
proves uniqueness and independence of representatives. -/
theorem shiftedExactTensorPullback_exists :
    ∃! μ : T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor,
      ∀ (E F : CochainComplex (ShiftedModuleCategory R) ℤ)
        (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F),
        ∃ (hE' : shiftedTensorResolving S
            ((uStar.mapHomologicalComplex (.up ℤ)).obj E))
          (hF' : shiftedTensorResolving S
            ((uStar.mapHomologicalComplex (.up ℤ)).obj F)),
          uStar.mapDerivedCategory.map
              (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) ≫
            μ.hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) ≫
            TS.tensor.map (Prod.mkHom (uStar.mapDerivedCategoryFactors.hom.app E)
              (uStar.mapDerivedCategoryFactors.hom.app F)) =
          uStar.mapDerivedCategoryFactors.hom.app ((shiftedTotalTensor R).obj (E, F)) ≫
            DerivedCategory.Q.map (k.totalIso R S RI uInv I c uStar hobj V am E F).inv ≫
            TS.representative.hom.app (⟨_, hE'⟩, ⟨_, hF'⟩) := by
  let LF := uStar.mapDerivedCategory
  let ε := uStar.mapDerivedCategoryFactorsh.hom
  have hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ShiftedModuleCategory R) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ LF uStar.mapDerivedCategoryFactorsh
  have hc (E : CochainComplex (ShiftedModuleCategory R) ℤ) :
      derivedPullbackComplexComparison uStar LF ε E =
        uStar.mapDerivedCategoryFactors.hom.app E := exactDerivedComparison uStar E
  have h := CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback
    uInv uPush adj I c uStar
    hobj hmap LF ε hLF (shiftedTensorResolving R) (shiftedTensorResolving S)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) T.tensor TS.tensor
    T.representative TS.representative k V am
  have hh := h.2
  simp only [hc, Functor.mapIso_inv, LF] at hh
  convert hh using 1
  rfl

/-- The canonical exact derived tensor comparison, fixed by its representative square.
Source: Stacks 07A4 (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def shiftedExactTensorPullback :
    T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor :=
  (shiftedExactTensorPullback_exists R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k).exists.choose

/-- All associator, Koszul symmetry and two-shift squares for exact pullback.
The proposition contains equations, rather than an unconstrained coherence hypothesis.
Source: Stacks 03EL/07A4 (blueprint: lem-pur-shifted-tensor-morphism-calculus). -/
def ShiftedPullbackCoherence
    (μ : T.tensor ⋙ uStar.mapDerivedCategory ≅
      (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor) : Prop :=
  GenericTensorPullbackCoherence T.tensor TS.tensor uStar.mapDerivedCategory
    (shiftedTensorCanonicalComparison R T) (shiftedTensorCanonicalComparison S TS)
    (derivedTensorAssociator R T) (derivedTensorSymmetry R T)
    (derivedTensorAssociator S TS) (derivedTensorSymmetry S TS) μ

/-- The complete ringed-topos clause: flatness preservation, all coherence diagrams,
 and B on the actual pulled-back flat degree-zero source sheaves.
Source: Stacks 03EL, 07A4, 0G7E, 0FPL/0FPM
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof: follow Steps 8--10 of the ten-step plan. Pure tensors
prove ordinary coherence, direct sums give the total-complex comparisons, and additivity
preserves every sign. The normalized derived tensor comparison descends the diagrams
by tensor descent. The preservation clause gives flatness of uStar P (apply it to P[0]).
Exactness gives the termwise derived functor used here. Naturality of the shift square
with respect to f and g proves the B equation; mapDerivedCategorySingleFunctor supplies
exactly the source identification with (uStar P)[0], including identity pullbacks. -/
def ShiftedTensorPullbackClause (a b : ℤ) : Prop :=
    (∀ P : ShiftedModuleCategory R, IsFlatOnSite P → IsFlatOnSite (uStar.obj P)) ∧
    ShiftedPullbackCoherence R T S TS uStar
      (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k) ∧
    ∀ (P Q : ShiftedModuleCategory R), IsFlatOnSite P → IsFlatOnSite Q →
      ∀ (K L : ShiftedDerivedCategory R)
        (f : shiftedDegreeZero R P ⟶ K⟦a⟧)
        (g : shiftedDegreeZero R Q ⟶ L⟦b⟧),
        uStar.mapDerivedCategory.map (shiftedTensorB R T a b _ _ K L f g) ≫
          (uStar.mapDerivedCategory.commShiftIso (a + b)).hom.app (T.tensor.obj (K, L)) ≫
          (CategoryTheory.shiftFunctor _ (a + b)).map
            ((shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
              hobj hmap V am k).hom.app (K, L)) =
        (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k).hom.app
            (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
          TS.tensor.map (Prod.mkHom ((uStar.mapDerivedCategorySingleFunctor 0).hom.app P)
            ((uStar.mapDerivedCategorySingleFunctor 0).hom.app Q)) ≫
          shiftedTensorB S TS a b _ _ (uStar.mapDerivedCategory.obj K)
            (uStar.mapDerivedCategory.obj L)
            ((uStar.mapDerivedCategorySingleFunctor 0).inv.app P ≫
              uStar.mapDerivedCategory.map f ≫
              (uStar.mapDerivedCategory.commShiftIso a).hom.app K)
            ((uStar.mapDerivedCategorySingleFunctor 0).inv.app Q ≫
              uStar.mapDerivedCategory.map g ≫
              (uStar.mapDerivedCategory.commShiftIso b).hom.app L)

section PullbackMorphismProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance 4001] shiftedOrdinaryTensor_additive
  shiftedOrdinaryTensor_objAdditive shiftedOrdinaryTensor_totalExists
attribute [local instance 4001] DerivedTensorConstraints.complexMonoidal
  DerivedTensorConstraints.complexMonoidalStruct CochainComplex.Monoidal.braidedCategory

attribute [local implicit_reducible] shiftedOrdinaryTensor shiftedTotalTensor
  CategoryTheory.prod.associator

attribute [local semireducible] TensorShiftNormalization TensorSymmetryNormalization
  TensorAssociatorNormalization GenericTensorPullbackCoherence
  siteDerivedTensorIndependentCoefficients shiftedTensorCanonicalComparison
  derivedTensorSymmetry derivedTensorAssociator
section ComplexPullbackProofs
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory CategoryTheory.Monoidal.induced
attribute [local instance 2000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor
attribute [local irreducible] CategoryTheory.CommShift₂Setup.int
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjMap₂CochainComplex
  CategoryTheory.Functor.instCommShiftCochainComplexIntObjFlipMap₂CochainComplex
include uPush adj hmap hlex in
private theorem shiftedPullback_flat :
    ∀ M : ShiftedModuleCategory R, IsFlatOnSite M → IsFlatOnSite (uStar.obj M) := by
  have hres := isKFlat_ringedToposPullback uInv uPush adj I c uStar hobj hmap
  intro M hm
  let P := (HomologicalComplex.single (ShiftedModuleCategory R) (.up ℤ) 0).obj M
  obtain ⟨hp, hf⟩ := (DerivedTensorConstraints.derived_tensor_model_closure R).2.2.2.1 M hm
  simpa only [Functor.mapHomologicalComplex_obj_X, P,
    HomologicalComplex.single_obj_X_self] using (hres P hp hf).2 0

private abbrev shiftedPullbackPresentation : CategoryTheory.CochainPullback.RingedPullback R S where
  uInv := uInv
  uPush := uPush
  adj := adj
  finiteLimits := inferInstance
  RI := RI
  I := I
  coefficient := c
  L := uStar
  hobj := hobj
  hmap := hmap
  V := V
  moduleAdj := am

private abbrev shiftedPullbackComparison : CategoryTheory.CochainPullback.Comparison
    (shiftedPullbackPresentation R S RI uInv uPush adj I c uStar hobj hmap V am) :=
  CochainTensorComparison.ofLanded R S RI uInv I c uStar hobj k

private theorem shiftedPullbackComparison_eq (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    (CategoryTheory.CochainPullback.comparison
      (shiftedPullbackPresentation R S RI uInv uPush adj I c uStar hobj hmap V am)
      (shiftedPullbackComparison R S RI uInv uPush adj I c uStar hobj hmap V am k) E F).hom =
      (k.totalIso R S RI uInv I c uStar hobj V am E F).inv := by
  rfl

set_option maxHeartbeats 800000 in
-- Compare the two presentations of the canonical total tensor comparison.
include uPush adj hmap hlex in
private theorem concrete_pairShift_compatibility (a b : ℤ)
    (E F : CochainComplex (ShiftedModuleCategory R) ℤ) :
    (k.totalIso R S RI uInv I c uStar hobj V am (E⟦a⟧) (F⟦b⟧)).inv ≫
      (shiftedTotalTensor S).map
        (Prod.mkHom (((uStar.mapHomologicalComplex (.up ℤ)).commShiftIso a).hom.app E)
          (((uStar.mapHomologicalComplex (.up ℤ)).commShiftIso b).hom.app F)) ≫
      (shiftedTensorComplexComparisonNatIso S a b).hom.app
        ((uStar.mapHomologicalComplex (.up ℤ)).obj E,
          (uStar.mapHomologicalComplex (.up ℤ)).obj F) =
    (uStar.mapHomologicalComplex (.up ℤ)).map
        ((shiftedTensorComplexComparisonNatIso R a b).hom.app (E, F)) ≫
      ((uStar.mapHomologicalComplex (.up ℤ)).commShiftIso (a + b)).hom.app
        ((shiftedTotalTensor R).obj (E, F)) ≫
      (shiftFunctor _ (a + b)).map (k.totalIso R S RI uInv I c uStar hobj V am E F).inv := by
  let f := shiftedPullbackPresentation R S RI uInv uPush adj I c uStar hobj hmap V am
  let kc := shiftedPullbackComparison R S RI uInv uPush adj I c uStar hobj hmap V am k
  have h := complex_pairShift_compatibility f kc a b E F
  have heq (X Y : CochainComplex (ShiftedModuleCategory R) ℤ) :
      (CategoryTheory.CochainPullback.comparison f kc X Y).hom =
        (k.totalIso R S RI uInv I c uStar hobj V am X Y).inv :=
    shiftedPullbackComparison_eq R S RI uInv uPush adj I c uStar hobj hmap V am k X Y
  simp only [heq] at h
  simp only [shiftedTensorComplexComparisonNatIso,
    totalTensorPairShift, KFlatFixedTensor.totalTensor, KFlatFixedTensor.ordinaryTensor,
    shiftedTotalTensor, shiftedOrdinaryTensor, CategoryTheory.CochainPullback.pull,
    f, shiftedPullbackPresentation, Functor.uncurry_obj_obj, Functor.comp_obj] at h ⊢
  convert h using 1 <;> rfl

end ComplexPullbackProofs

private theorem shiftedTensor_pullback_of_coherence (a b : ℤ)
    (hflat : ∀ P : ShiftedModuleCategory R, IsFlatOnSite P → IsFlatOnSite (uStar.obj P))
    (hc : ShiftedPullbackCoherence R T S TS uStar
      (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k)) :
    ShiftedTensorPullbackClause R T S RI TS uInv uPush adj I c uStar
      hobj hmap V am k a b := by
  refine ⟨hflat, hc, ?_⟩
  intro P Q hP hQ K L f g
  let F := uStar.mapDerivedCategory
  let μ := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k
  unfold ShiftedPullbackCoherence GenericTensorPullbackCoherence at hc
  have hs := hc.2.2 a b K L
  have hn := μ.hom.naturality (Prod.mkHom f g)
  change F.map (T.tensor.map (Prod.mkHom f g)) ≫ μ.hom.app (K⟦a⟧, L⟦b⟧) =
    μ.hom.app (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫
      TS.tensor.map (Prod.mkHom (F.map f) (F.map g)) at hn
  have hrebase :
      TS.tensor.map (Prod.mkHom ((uStar.mapDerivedCategorySingleFunctor 0).hom.app P)
          ((uStar.mapDerivedCategorySingleFunctor 0).hom.app Q)) ≫
        TS.tensor.map (Prod.mkHom
          ((uStar.mapDerivedCategorySingleFunctor 0).inv.app P ≫ F.map f ≫
            (F.commShiftIso a).hom.app K)
          ((uStar.mapDerivedCategorySingleFunctor 0).inv.app Q ≫ F.map g ≫
            (F.commShiftIso b).hom.app L)) =
      TS.tensor.map (Prod.mkHom (F.map f) (F.map g)) ≫
        TS.tensor.map (Prod.mkHom ((F.commShiftIso a).hom.app K)
          ((F.commShiftIso b).hom.app L)) := by
    rw [← TS.tensor.map_comp, ← TS.tensor.map_comp]
    congr 1
    apply Prod.ext <;> simp only [prod_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [shiftedTensorB, Functor.map_comp, Category.assoc]
  change F.map (T.tensor.map (Prod.mkHom f g)) ≫
      F.map ((shiftedTensorCanonicalComparison R T a b).hom.app (K, L)) ≫
      (F.commShiftIso (a + b)).hom.app _ ≫
      (shiftFunctor _ (a + b)).map (μ.hom.app (K, L)) = _
  rw [hs, ← Category.assoc, hn]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ μ.hom.app (shiftedDegreeZero R P, shiftedDegreeZero R Q) ≫ z ≫
      (shiftedTensorCanonicalComparison S TS a b).hom.app (F.obj K, F.obj L)) hrebase.symm
private abbrev pullbackModel (E : (shiftedTensorResolving R).FullSubcategory) :
    (shiftedTensorResolving S).FullSubcategory :=
  ⟨(uStar.mapHomologicalComplex (.up ℤ)).obj E.obj,
    isKFlat_ringedToposPullback uInv uPush adj I c uStar hobj hmap E.obj
      E.property.1 E.property.2⟩

private theorem pullback_normalization
    (E F : (shiftedTensorResolving R).FullSubcategory) :
    uStar.mapDerivedCategory.map (T.representative.hom.app (E, F)) ≫
      (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
        hobj hmap V am k).hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≫
      TS.tensor.map (Prod.mkHom (uStar.mapDerivedCategoryFactors.hom.app E.obj)
        (uStar.mapDerivedCategoryFactors.hom.app F.obj)) =
    uStar.mapDerivedCategoryFactors.hom.app ((shiftedTotalTensor R).obj (E.obj, F.obj)) ≫
      DerivedCategory.Q.map (k.totalIso R S RI uInv I c uStar hobj V am E.obj F.obj).inv ≫
      TS.representative.hom.app
        (pullbackModel R S RI uInv uPush adj I c uStar hobj hmap E,
          pullbackModel R S RI uInv uPush adj I c uStar hobj hmap F) := by
  have hn := (shiftedExactTensorPullback_exists R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k).exists.choose_spec
  obtain ⟨_, _, hn⟩ := hn E.obj F.obj E.property F.property
  exact hn

set_option maxHeartbeats 1600000 in
-- Paste the representative comparison squares before cancellation.
private theorem pullback_symmetry_on_models
    (E F : (shiftedTensorResolving R).FullSubcategory) :
    let U := uStar.mapDerivedCategory
    let m := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
      hobj hmap V am k
    U.map ((derivedTensorSymmetry R T).hom.app
        (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj)) ≫
      m.hom.app (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj E.obj) =
    m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≫
      (derivedTensorSymmetry S TS).hom.app
        (U.obj (DerivedCategory.Q.obj E.obj), U.obj (DerivedCategory.Q.obj F.obj)) := by
  dsimp only
  let U := uStar.mapDerivedCategory
  let m := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k
  let f := shiftedPullbackPresentation R S RI uInv uPush adj I c uStar hobj hmap V am
  let kc := shiftedPullbackComparison R S RI uInv uPush adj I c uStar hobj hmap V am k
  let pm := pullbackModel R S RI uInv uPush adj I c uStar hobj hmap
  let e := uStar.mapDerivedCategoryFactors
  let sf := TS.tensor.map
    (Prod.mkHom (e.hom.app F.obj) (e.hom.app E.obj))
  have : IsIso sf := by
    change IsIso ((TS.tensor.mapIso (Iso.prod (e.app F.obj) (e.app E.obj))).hom)
    infer_instance
  apply (cancel_epi (U.map (T.representative.hom.app (E, F)))).1
  apply (cancel_mono sf).1
  have hm := pullback_normalization R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k E F
  have hm' := pullback_normalization R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k F E
  have hn := (derivedTensorSymmetry S TS).hom.naturality
    (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj))
  change TS.tensor.map (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj)) ≫
      (derivedTensorSymmetry S TS).hom.app
        (DerivedCategory.Q.obj (pm E).obj, DerivedCategory.Q.obj (pm F).obj) =
    (derivedTensorSymmetry S TS).hom.app
      (U.obj (DerivedCategory.Q.obj E.obj), U.obj (DerivedCategory.Q.obj F.obj)) ≫ sf at hn
  have he := e.hom.naturality (shiftedComplexSwap R E.obj F.obj).hom
  change U.map (DerivedCategory.Q.map (shiftedComplexSwap R E.obj F.obj).hom) ≫
      e.hom.app ((shiftedTotalTensor R).obj (F.obj, E.obj)) =
    e.hom.app ((shiftedTotalTensor R).obj (E.obj, F.obj)) ≫
      DerivedCategory.Q.map
        ((uStar.mapHomologicalComplex (.up ℤ)).map (shiftedComplexSwap R E.obj F.obj).hom) at he
  have hc :
      (uStar.mapHomologicalComplex (.up ℤ)).map (shiftedComplexSwap R E.obj F.obj).hom ≫
          (k.totalIso R S RI uInv I c uStar hobj V am F.obj E.obj).inv =
        (k.totalIso R S RI uInv I c uStar hobj V am E.obj F.obj).inv ≫
          (shiftedComplexSwap S (pm E).obj (pm F).obj).hom := by
    simp only [swap_native]
    convert (CategoryTheory.CochainPullback.cochainComparison_monoidal f kc).2.2.1
      E.obj F.obj using 1 <;> rfl
  simp only [sf, Category.assoc]
  erw [← hn]
  erw [← U.map_comp_assoc, symmetry_normalization R T E.obj F.obj E.property F.property,
    U.map_comp]
  simp only [Category.assoc]
  erw [hm', reassoc_of% he]
  erw [← DerivedCategory.Q.map_comp_assoc, hc, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  erw [← symmetry_normalization S TS (pm E).obj (pm F).obj (pm E).property (pm F).property]
  erw [← reassoc_of% hm]

set_option maxHeartbeats 1600000 in
-- Paste the representative comparison squares before cancellation.
private theorem pullback_associativity_on_models
    (E F G : (shiftedTensorResolving R).FullSubcategory) :
    let U := uStar.mapDerivedCategory
    let m := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
      hobj hmap V am k
    U.map ((derivedTensorAssociator R T).hom.app
        ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj), DerivedCategory.Q.obj G.obj)) ≫
      m.hom.app (DerivedCategory.Q.obj E.obj,
        T.tensor.obj (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)) ≫
      TS.tensor.map (Prod.mkHom (𝟙 (U.obj (DerivedCategory.Q.obj E.obj)))
        (m.hom.app (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj))) =
    m.hom.app (T.tensor.obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
        DerivedCategory.Q.obj G.obj) ≫
      TS.tensor.map (Prod.mkHom
        (m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj))
        (𝟙 (U.obj (DerivedCategory.Q.obj G.obj)))) ≫
      (derivedTensorAssociator S TS).hom.app
        ((U.obj (DerivedCategory.Q.obj E.obj), U.obj (DerivedCategory.Q.obj F.obj)),
          U.obj (DerivedCategory.Q.obj G.obj)) := by
  dsimp only
  letI := monoidalCategory R
  letI := symmetricCategory R
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R
  letI := monoidalCategory S
  letI := symmetricCategory S
  letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive S
  let U := uStar.mapDerivedCategory
  let m := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k
  let f := shiftedPullbackPresentation R S RI uInv uPush adj I c uStar hobj hmap V am
  let kc := shiftedPullbackComparison R S RI uInv uPush adj I c uStar hobj hmap V am k
  let pm := pullbackModel R S RI uInv uPush adj I c uStar hobj hmap
  let EF := totalModel R E F
  let FG := totalModel R F G
  let ES := pm E
  let FS := pm F
  let GS := pm G
  let EFS := totalModel S ES FS
  let FGS := totalModel S FS GS
  let bEF := T.representative.app (E, F)
  let bFG := T.representative.app (F, G)
  let bL := T.representative.app (EF, G)
  let bR := T.representative.app (E, FG)
  let aEF := TS.representative.app (ES, FS)
  let aFG := TS.representative.app (FS, GS)
  let aL := TS.representative.app (EFS, GS)
  let aR := TS.representative.app (ES, FGS)
  let aL₀ := TS.representative.app (pm EF, GS)
  let aR₀ := TS.representative.app (ES, pm FG)
  let lB := bL ≪≫ T.tensor.mapIso (Iso.prod bEF (Iso.refl (DerivedCategory.Q.obj G.obj)))
  let rB := bR ≪≫ T.tensor.mapIso (Iso.prod (Iso.refl (DerivedCategory.Q.obj E.obj)) bFG)
  let lA := aL ≪≫ TS.tensor.mapIso (Iso.prod aEF (Iso.refl (DerivedCategory.Q.obj GS.obj)))
  let rA := aR ≪≫ TS.tensor.mapIso (Iso.prod (Iso.refl (DerivedCategory.Q.obj ES.obj)) aFG)
  let e := uStar.mapDerivedCategoryFactors
  let comp (A B : (shiftedTensorResolving R).FullSubcategory) :
      (uStar.mapHomologicalComplex (.up ℤ)).obj ((shiftedTotalTensor R).obj (A.obj, B.obj)) ⟶
        (shiftedTotalTensor S).obj ((pm A).obj, (pm B).obj) :=
    (k.totalIso R S RI uInv I c uStar hobj V am A.obj B.obj).inv
  let cEF := comp E F
  let cFG := comp F G
  let cL := comp EF G
  let cR := comp E FG
  let eL := e.hom.app ((totalModel R EF G).obj) ≫
    DerivedCategory.Q.map cL ≫ DerivedCategory.Q.map (HomologicalComplex.tensorHom cEF (𝟙 GS.obj))
  let eR := e.hom.app ((totalModel R E FG).obj) ≫
    DerivedCategory.Q.map cR ≫ DerivedCategory.Q.map (HomologicalComplex.tensorHom (𝟙 ES.obj) cFG)
  have hm (A B : (shiftedTensorResolving R).FullSubcategory) :
      U.map (T.representative.app (A, B)).hom ≫
        m.hom.app (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) ≫
        TS.tensor.map (Prod.mkHom (e.hom.app A.obj) (e.hom.app B.obj)) =
      e.hom.app ((totalModel R A B).obj) ≫
        DerivedCategory.Q.map (comp A B) ≫
        (TS.representative.app (pm A, pm B)).hom := by
    simpa only [Iso.app_hom, U, m, e, pm, comp, totalModel] using
      pullback_normalization R T S RI TS uInv uPush adj I c uStar hobj hmap V am k A B
  have hB : lB.hom ≫ (derivedTensorAssociator R T).hom.app
      ((DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj), DerivedCategory.Q.obj G.obj) =
      DerivedCategory.Q.map (HomologicalComplex.associator E.obj F.obj G.obj).hom ≫ rB.hom := by
    simpa only [lB, rB, bL, bR, bEF, bFG, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Iso.app_hom, leftModelRepresentative,
      rightModelRepresentative, Functor.comp_obj, Functor.prod_obj,
      ObjectProperty.ι_obj, EF, FG, EFS, FGS, totalModel, Category.assoc] using
      associator_normalization R T E F G
  have hA : lA.hom ≫ (derivedTensorAssociator S TS).hom.app
      ((DerivedCategory.Q.obj ES.obj, DerivedCategory.Q.obj FS.obj), DerivedCategory.Q.obj GS.obj) =
      DerivedCategory.Q.map (HomologicalComplex.associator ES.obj FS.obj GS.obj).hom ≫ rA.hom := by
    simpa only [lA, rA, aL, aR, aEF, aFG, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Iso.app_hom, leftModelRepresentative,
      rightModelRepresentative, Functor.comp_obj, Functor.prod_obj,
      ObjectProperty.ι_obj, EF, FG, EFS, FGS, totalModel, Category.assoc] using
      associator_normalization S TS ES FS GS
  have hnL := TS.representative.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk cEF : pm EF ⟶ EFS) (𝟙 GS))
  have hnR := TS.representative.hom.naturality
    (Prod.mkHom (𝟙 ES) (ObjectProperty.homMk cFG : pm FG ⟶ FGS))
  change DerivedCategory.Q.map ((shiftedTotalTensor S).map (Prod.mkHom cEF (𝟙 GS.obj))) ≫
      aL.hom = aL₀.hom ≫ TS.tensor.map (Prod.mkHom (DerivedCategory.Q.map cEF)
        (DerivedCategory.Q.map (𝟙 GS.obj))) at hnL
  change DerivedCategory.Q.map ((shiftedTotalTensor S).map (Prod.mkHom (𝟙 ES.obj) cFG)) ≫
      aR.hom = aR₀.hom ≫ TS.tensor.map (Prod.mkHom (DerivedCategory.Q.map (𝟙 ES.obj))
        (DerivedCategory.Q.map cFG)) at hnR
  replace hnL := hnL.trans (congrArg
    (fun z ↦ aL₀.hom ≫ TS.tensor.map (Prod.mkHom (DerivedCategory.Q.map cEF) z))
    (DerivedCategory.Q.map_id GS.obj))
  replace hnR := hnR.trans (congrArg
    (fun z ↦ aR₀.hom ≫ TS.tensor.map (Prod.mkHom z (DerivedCategory.Q.map cFG)))
    (DerivedCategory.Q.map_id ES.obj))
  simp only [total_map] at hnL hnR
  let mL := m.hom.app
    (T.tensor.obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
      DerivedCategory.Q.obj G.obj) ≫ TS.tensor.map (Prod.mkHom
        (m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj))
        (𝟙 (U.obj (DerivedCategory.Q.obj G.obj))))
  let mR := m.hom.app
    (DerivedCategory.Q.obj E.obj,
      T.tensor.obj (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)) ≫
    TS.tensor.map (Prod.mkHom (𝟙 (U.obj (DerivedCategory.Q.obj E.obj)))
      (m.hom.app (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)))
  have hL : U.map lB.hom ≫ mL ≫
      TS.tensor.map (Prod.mkHom
        (TS.tensor.map (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj)))
        (e.hom.app G.obj)) = eL ≫ lA.hom := by
    have hn := m.hom.naturality
      (Prod.mkHom bEF.hom (𝟙 (DerivedCategory.Q.obj G.obj)))
    change U.map (T.tensor.map (Prod.mkHom bEF.hom (𝟙 _))) ≫
        m.hom.app (T.tensor.obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj),
          DerivedCategory.Q.obj G.obj) =
      m.hom.app (DerivedCategory.Q.obj EF.obj, DerivedCategory.Q.obj G.obj) ≫
        TS.tensor.map (Prod.mkHom (U.map bEF.hom) (U.map (𝟙 _))) at hn
    replace hn := hn.trans (congrArg
      (fun z ↦ m.hom.app (DerivedCategory.Q.obj EF.obj, DerivedCategory.Q.obj G.obj) ≫
        TS.tensor.map (Prod.mkHom (U.map bEF.hom) z))
      (U.map_id (DerivedCategory.Q.obj G.obj)))
    calc
      U.map lB.hom ≫ mL ≫ TS.tensor.map (Prod.mkHom
          (TS.tensor.map (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj)))
          (e.hom.app G.obj)) = U.map bL.hom ≫ m.hom.app
          (DerivedCategory.Q.obj EF.obj, DerivedCategory.Q.obj G.obj) ≫
          TS.tensor.map (Prod.mkHom
            (U.map bEF.hom ≫ m.hom.app
              (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≫
              TS.tensor.map (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj)))
            (e.hom.app G.obj)) := by
        simp only [lB, mL, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, U.map_comp, Category.assoc]
        erw [reassoc_of% hn]
        simp only [← TS.tensor.map_comp, prod_comp, Prod.mkHom]
        erw [Category.id_comp, Category.id_comp]
      _ = U.map bL.hom ≫ m.hom.app
          (DerivedCategory.Q.obj EF.obj, DerivedCategory.Q.obj G.obj) ≫
          TS.tensor.map (Prod.mkHom
            (e.hom.app EF.obj ≫ DerivedCategory.Q.map cEF ≫ aEF.hom)
            (e.hom.app G.obj)) := by erw [hm E F]
      _ = (U.map bL.hom ≫ m.hom.app
          (DerivedCategory.Q.obj EF.obj, DerivedCategory.Q.obj G.obj) ≫
          TS.tensor.map (Prod.mkHom (e.hom.app EF.obj) (e.hom.app G.obj))) ≫
          TS.tensor.map (Prod.mkHom (DerivedCategory.Q.map cEF ≫ aEF.hom) (𝟙 _)) := by
        simp only [Category.assoc, ← TS.tensor.map_comp, prod_comp, Prod.mkHom,
          Category.comp_id]
      _ = eL ≫ lA.hom := by
        erw [hm EF G, shiftedTensorMap_comp_left]
        simp only [Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Category.assoc]
        rfl
  have hR : U.map rB.hom ≫ mR ≫
      TS.tensor.map (Prod.mkHom (e.hom.app E.obj)
        (TS.tensor.map (Prod.mkHom (e.hom.app F.obj) (e.hom.app G.obj)))) = eR ≫ rA.hom := by
    have hn := m.hom.naturality
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj E.obj)) bFG.hom)
    change U.map (T.tensor.map (Prod.mkHom (𝟙 _) bFG.hom)) ≫
        m.hom.app (DerivedCategory.Q.obj E.obj,
          T.tensor.obj (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj)) =
      m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj FG.obj) ≫
        TS.tensor.map (Prod.mkHom (U.map (𝟙 _)) (U.map bFG.hom)) at hn
    replace hn := hn.trans (congrArg
      (fun z ↦ m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj FG.obj) ≫
        TS.tensor.map (Prod.mkHom z (U.map bFG.hom)))
      (U.map_id (DerivedCategory.Q.obj E.obj)))
    calc
      U.map rB.hom ≫ mR ≫ TS.tensor.map (Prod.mkHom (e.hom.app E.obj)
          (TS.tensor.map (Prod.mkHom (e.hom.app F.obj) (e.hom.app G.obj)))) =
          U.map bR.hom ≫ m.hom.app
          (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj FG.obj) ≫
          TS.tensor.map (Prod.mkHom (e.hom.app E.obj)
            (U.map bFG.hom ≫ m.hom.app
              (DerivedCategory.Q.obj F.obj, DerivedCategory.Q.obj G.obj) ≫
              TS.tensor.map (Prod.mkHom (e.hom.app F.obj) (e.hom.app G.obj)))) := by
        simp only [rB, mR, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, U.map_comp, Category.assoc]
        erw [reassoc_of% hn]
        simp only [← TS.tensor.map_comp, prod_comp, Prod.mkHom]
        erw [Category.id_comp, Category.id_comp]
      _ = U.map bR.hom ≫ m.hom.app
          (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj FG.obj) ≫
          TS.tensor.map (Prod.mkHom (e.hom.app E.obj)
            (e.hom.app FG.obj ≫ DerivedCategory.Q.map cFG ≫ aFG.hom)) := by erw [hm F G]
      _ = (U.map bR.hom ≫ m.hom.app
          (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj FG.obj) ≫
          TS.tensor.map (Prod.mkHom (e.hom.app E.obj) (e.hom.app FG.obj))) ≫
          TS.tensor.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cFG ≫ aFG.hom)) := by
        simp only [Category.assoc, ← TS.tensor.map_comp, prod_comp, Prod.mkHom,
          Category.comp_id]
      _ = eR ≫ rA.hom := by
        erw [hm E FG, shiftedTensorMap_comp_right]
        simp only [Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
          Iso.refl_hom, Category.assoc]
        rfl
  have hC : U.map (DerivedCategory.Q.map (HomologicalComplex.associator E.obj F.obj G.obj).hom) ≫
      eR = eL ≫ DerivedCategory.Q.map (HomologicalComplex.associator ES.obj FS.obj GS.obj).hom := by
    have he := e.hom.naturality (HomologicalComplex.associator E.obj F.obj G.obj).hom
    change U.map (DerivedCategory.Q.map (HomologicalComplex.associator E.obj F.obj G.obj).hom) ≫
        e.hom.app ((totalModel R E FG).obj) =
      e.hom.app ((totalModel R EF G).obj) ≫
        DerivedCategory.Q.map ((uStar.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.associator E.obj F.obj G.obj).hom) at he
    have hc :
        (uStar.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.associator E.obj F.obj G.obj).hom ≫
          cR ≫ HomologicalComplex.tensorHom (𝟙 ES.obj) cFG =
        cL ≫ HomologicalComplex.tensorHom cEF (𝟙 GS.obj) ≫
          (HomologicalComplex.associator ES.obj FS.obj GS.obj).hom := by
      convert (CategoryTheory.CochainPullback.cochainComparison_monoidal f kc).2.1
        E.obj F.obj G.obj using 1 <;> rfl
    dsimp only [eL, eR]
    erw [reassoc_of% he]
    simpa only [DerivedCategory.Q.map_comp, Category.assoc] using congrArg
      (fun z ↦ e.hom.app ((totalModel R EF G).obj) ≫ DerivedCategory.Q.map z) hc
  let vL := TS.tensor.map (Prod.mkHom
    (TS.tensor.map (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj))) (e.hom.app G.obj))
  let vR := TS.tensor.map (Prod.mkHom (e.hom.app E.obj)
    (TS.tensor.map (Prod.mkHom (e.hom.app F.obj) (e.hom.app G.obj))))
  have : IsIso vR := by
    change IsIso ((TS.tensor.mapIso (Iso.prod (e.app E.obj)
      (TS.tensor.mapIso (Iso.prod (e.app F.obj) (e.app G.obj))))).hom)
    infer_instance
  apply (cancel_epi (U.map lB.hom)).1
  apply (cancel_mono vR).1
  have hnat := (derivedTensorAssociator S TS).hom.naturality
    (Prod.mkHom (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj)) (e.hom.app G.obj))
  change vL ≫ (derivedTensorAssociator S TS).hom.app
      ((DerivedCategory.Q.obj ES.obj, DerivedCategory.Q.obj FS.obj), DerivedCategory.Q.obj GS.obj) =
    (derivedTensorAssociator S TS).hom.app
      ((U.obj (DerivedCategory.Q.obj E.obj), U.obj (DerivedCategory.Q.obj F.obj)),
        U.obj (DerivedCategory.Q.obj G.obj)) ≫ vR at hnat
  simp only [Category.assoc]
  calc
    _ = U.map (DerivedCategory.Q.map (HomologicalComplex.associator E.obj F.obj G.obj).hom) ≫
        U.map rB.hom ≫ mR ≫ vR := by
      erw [← U.map_comp_assoc, hB, U.map_comp]
      simp only [mR, Category.assoc]
      rfl
    _ = U.map (DerivedCategory.Q.map (HomologicalComplex.associator E.obj F.obj G.obj).hom) ≫
        eR ≫ rA.hom := by erw [hR]
    _ = eL ≫ DerivedCategory.Q.map
        (HomologicalComplex.associator ES.obj FS.obj GS.obj).hom ≫ rA.hom := by
      erw [reassoc_of% hC]
    _ = eL ≫ lA.hom ≫ (derivedTensorAssociator S TS).hom.app
        ((DerivedCategory.Q.obj ES.obj, DerivedCategory.Q.obj FS.obj),
          DerivedCategory.Q.obj GS.obj) := by
      erw [hA]
    _ = U.map lB.hom ≫ mL ≫ vL ≫ (derivedTensorAssociator S TS).hom.app
        ((DerivedCategory.Q.obj ES.obj, DerivedCategory.Q.obj FS.obj),
          DerivedCategory.Q.obj GS.obj) := by
      erw [reassoc_of% hL]
    _ = _ := by
      erw [hnat]
      simp only [mL, Category.assoc]
      rfl

set_option maxHeartbeats 1600000 in
-- Paste the representative comparison squares before cancellation.
private theorem pullback_shift_on_models (a b : ℤ)
    (E F : (shiftedTensorResolving R).FullSubcategory) :
    let U := uStar.mapDerivedCategory
    let m := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k
    U.map ((shiftedTensorCanonicalComparison R T a b).hom.app
        (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj)) ≫
      (U.commShiftIso (a + b)).hom.app
        (T.tensor.obj (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj)) ≫
      (shiftFunctor _ (a + b)).map
        (m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj)) =
    m.hom.app ((DerivedCategory.Q.obj E.obj)⟦a⟧, (DerivedCategory.Q.obj F.obj)⟦b⟧) ≫
      TS.tensor.map (Prod.mkHom ((U.commShiftIso a).hom.app (DerivedCategory.Q.obj E.obj))
        ((U.commShiftIso b).hom.app (DerivedCategory.Q.obj F.obj))) ≫
      (shiftedTensorCanonicalComparison S TS a b).hom.app
        (U.obj (DerivedCategory.Q.obj E.obj), U.obj (DerivedCategory.Q.obj F.obj)) := by
  dsimp only
  let q : CochainComplex (ShiftedModuleCategory R) ℤ ⥤ ShiftedDerivedCategory R :=
    DerivedCategory.Q
  let qs : CochainComplex (ShiftedModuleCategory S) ℤ ⥤ ShiftedDerivedCategory S :=
    DerivedCategory.Q
  let U := uStar.mapDerivedCategory
  let p := uStar.mapHomologicalComplex (.up ℤ)
  let e := uStar.mapDerivedCategoryFactors
  let m := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k
  let pm := pullbackModel R S RI uInv uPush adj I c uStar hobj hmap
  let Ea : (shiftedTensorResolving R).FullSubcategory :=
    ⟨E.obj⟦a⟧, shiftedModelShift_closed R E a⟩
  let Fb : (shiftedTensorResolving R).FullSubcategory :=
    ⟨F.obj⟦b⟧, shiftedModelShift_closed R F b⟩
  let ES := pm E
  let FS := pm F
  let ESs : (shiftedTensorResolving S).FullSubcategory :=
    ⟨ES.obj⟦a⟧, shiftedModelShift_closed S ES a⟩
  let FSs : (shiftedTensorResolving S).FullSubcategory :=
    ⟨FS.obj⟦b⟧, shiftedModelShift_closed S FS b⟩
  let EF := (shiftedTotalTensor R).obj (E.obj, F.obj)
  let EFs := (shiftedTotalTensor R).obj (Ea.obj, Fb.obj)
  let EFS := (shiftedTotalTensor S).obj (ES.obj, FS.obj)
  let ρ : q.obj EF ⟶ T.tensor.obj (q.obj E.obj, q.obj F.obj) := T.representative.hom.app (E, F)
  let ρs : q.obj EFs ⟶ T.tensor.obj (q.obj Ea.obj, q.obj Fb.obj) :=
    T.representative.hom.app (Ea, Fb)
  let ρS : qs.obj EFS ⟶ TS.tensor.obj (qs.obj ES.obj, qs.obj FS.obj) :=
    TS.representative.hom.app (ES, FS)
  let ρSs : qs.obj ((shiftedTotalTensor S).obj (ESs.obj, FSs.obj)) ⟶
      TS.tensor.obj (qs.obj ESs.obj, qs.obj FSs.obj) := TS.representative.hom.app (ESs, FSs)
  let ρSraw : qs.obj ((shiftedTotalTensor S).obj ((pm Ea).obj, (pm Fb).obj)) ⟶
      TS.tensor.obj (qs.obj (pm Ea).obj, qs.obj (pm Fb).obj) :=
    TS.representative.hom.app (pm Ea, pm Fb)
  let eE := e.hom.app E.obj
  let eF := e.hom.app F.obj
  let eEa := e.hom.app Ea.obj
  let eFb := e.hom.app Fb.obj
  let δE := (p.commShiftIso a).hom.app E.obj
  let δF := (p.commShiftIso b).hom.app F.obj
  let δEF := (p.commShiftIso (a + b)).hom.app EF
  let κE := (q.commShiftIso a).hom.app E.obj
  let κF := (q.commShiftIso b).hom.app F.obj
  let κEF := (q.commShiftIso (a + b)).hom.app EF
  let κSE := (qs.commShiftIso a).hom.app ES.obj
  let κSF := (qs.commShiftIso b).hom.app FS.obj
  let κSp := (qs.commShiftIso (a + b)).hom.app (p.obj EF)
  let κSS := (qs.commShiftIso (a + b)).hom.app EFS
  let κU := (U.commShiftIso (a + b)).hom.app (q.obj EF)
  let κUT := (U.commShiftIso (a + b)).hom.app (T.tensor.obj (q.obj E.obj, q.obj F.obj))
  let κUE := (U.commShiftIso a).hom.app (q.obj E.obj)
  let κUF := (U.commShiftIso b).hom.app (q.obj F.obj)
  let kR := T.tensor.map (Prod.mkHom κE κF)
  let kU := TS.tensor.map (Prod.mkHom κUE κUF)
  let ku := TS.tensor.map (Prod.mkHom (U.map κE) (U.map κF))
  let kS := TS.tensor.map (Prod.mkHom κSE κSF)
  let v := TS.tensor.map (Prod.mkHom eE eF)
  let vs := TS.tensor.map (Prod.mkHom eEa eFb)
  let w := TS.tensor.map (Prod.mkHom (qs.map δE) (qs.map δF))
  let vshift := TS.tensor.map
    (Prod.mkHom ((shiftFunctor _ a).map eE) ((shiftFunctor _ b).map eF))
  let tR := (shiftedTensorCanonicalComparison R T a b).hom.app (q.obj E.obj, q.obj F.obj)
  let tS := (shiftedTensorCanonicalComparison S TS a b).hom.app
    (U.obj (q.obj E.obj), U.obj (q.obj F.obj))
  let tSp := (shiftedTensorCanonicalComparison S TS a b).hom.app (qs.obj ES.obj, qs.obj FS.obj)
  let cR := (shiftedTensorComplexComparisonNatIso R a b).hom.app (E.obj, F.obj)
  let cS := (shiftedTensorComplexComparisonNatIso S a b).hom.app (ES.obj, FS.obj)
  let c0 : p.obj EF ⟶ EFS := (k.totalIso R S RI uInv I c uStar hobj V am E.obj F.obj).inv
  let cs : p.obj EFs ⟶ (shiftedTotalTensor S).obj ((pm Ea).obj, (pm Fb).obj) :=
    (k.totalIso R S RI uInv I c uStar hobj V am Ea.obj Fb.obj).inv
  let cd := (shiftedTotalTensor S).map (Prod.mkHom δE δF)
  let sh := shiftFunctor (ShiftedDerivedCategory S) (a + b)
  have hε (n : ℤ) (X : CochainComplex (ShiftedModuleCategory R) ℤ) :
      U.map ((q.commShiftIso n).hom.app X) ≫
        (U.commShiftIso n).hom.app (q.obj X) ≫
        (shiftFunctor _ n).map (e.hom.app X) =
      e.hom.app (X⟦n⟧) ≫ qs.map ((p.commShiftIso n).hom.app X) ≫
        (qs.commShiftIso n).hom.app (p.obj X) := by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      (NatTrans.shift_app_comm e.hom n X)
  have hFactor : ku ≫ kU ≫ vshift = vs ≫ w ≫ kS := by
    simp only [ku, kU, vshift, vs, w, kS, ← TS.tensor.map_comp, prod_comp, Category.assoc]
    congr 1
    apply Prod.ext
    · exact hε a E.obj
    · exact hε b F.obj
  have hm := pullback_normalization R T S RI TS uInv uPush adj I c uStar hobj hmap V am k E F
  have hms := pullback_normalization R T S RI TS uInv uPush adj I c uStar hobj hmap V am k Ea Fb
  have htR := shift_normalization R T a b E.obj F.obj E.property F.property Ea.property Fb.property
  have htS := shift_normalization S TS a b ES.obj FS.obj ES.property FS.property
    ESs.property FSs.property
  change U.map ρ ≫ m.hom.app (q.obj E.obj, q.obj F.obj) ≫ v =
    e.hom.app EF ≫ qs.map c0 ≫ ρS at hm
  change U.map ρs ≫ m.hom.app (q.obj Ea.obj, q.obj Fb.obj) ≫ vs =
    e.hom.app EFs ≫ qs.map cs ≫ ρSraw at hms
  change ρs ≫ kR ≫ tR = q.map cR ≫ κEF ≫ (shiftFunctor _ (a + b)).map ρ at htR
  change ρSs ≫ kS ≫ tSp = qs.map cS ≫ κSS ≫ sh.map ρS at htS
  have hn := m.hom.naturality (Prod.mkHom κE κF)
  change U.map kR ≫ m.hom.app ((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧) =
    m.hom.app (q.obj Ea.obj, q.obj Fb.obj) ≫ ku at hn
  have htn := (shiftedTensorCanonicalComparison S TS a b).hom.naturality (Prod.mkHom eE eF)
  change vshift ≫ tSp = tS ≫ sh.map v at htn
  have hκ := (U.commShiftIso (a + b)).hom.naturality ρ
  change U.map ((shiftFunctor _ (a + b)).map ρ) ≫ κUT = κU ≫ sh.map (U.map ρ) at hκ
  have hrS := TS.representative.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk δE : pm Ea ⟶ ESs)
      (ObjectProperty.homMk δF : pm Fb ⟶ FSs))
  change qs.map cd ≫ ρSs = ρSraw ≫ w at hrS
  have hL : U.map ρs ≫ U.map kR ≫ (U.map tR ≫ κUT ≫
      sh.map (m.hom.app (q.obj E.obj, q.obj F.obj))) ≫ sh.map v =
      U.map (q.map cR) ≫ U.map κEF ≫ κU ≫ sh.map (e.hom.app EF) ≫
        sh.map (qs.map c0) ≫ sh.map ρS := by
    have h := congrArg (fun z ↦ U.map z ≫ κUT ≫
      sh.map (m.hom.app (q.obj E.obj, q.obj F.obj)) ≫ sh.map v) htR
    simp only [U.map_comp, Category.assoc] at h
    erw [reassoc_of% hκ] at h
    have hb := congrArg (fun z ↦ U.map (q.map cR) ≫ U.map κEF ≫ κU ≫ sh.map z) hm
    simp only [sh.map_comp, Category.assoc] at hb
    simpa only [Category.assoc] using h.trans hb
  have hR : U.map ρs ≫ U.map kR ≫
      (m.hom.app ((q.obj E.obj)⟦a⟧, (q.obj F.obj)⟦b⟧) ≫ kU ≫ tS) ≫ sh.map v =
      e.hom.app EFs ≫ qs.map cs ≫ qs.map cd ≫ qs.map cS ≫ κSS ≫ sh.map ρS := by
    simp only [Category.assoc]
    erw [reassoc_of% hn, ← htn, reassoc_of% hFactor, reassoc_of% hms,
      ← reassoc_of% hrS, htS]
  have hεEF := hε (a + b) EF
  have he := e.hom.naturality cR
  change U.map (q.map cR) ≫ e.hom.app (EF⟦a + b⟧) =
    e.hom.app EFs ≫ qs.map (p.map cR) at he
  have hk := (qs.commShiftIso (a + b)).hom.naturality c0
  change qs.map ((shiftFunctor _ (a + b)).map c0) ≫ κSS =
    κSp ≫ sh.map (qs.map c0) at hk
  erw [reassoc_of% hεEF, reassoc_of% he, ← reassoc_of% hk] at hL
  have hc : cs ≫ cd ≫ cS = p.map cR ≫ δEF ≫ (shiftFunctor _ (a + b)).map c0 := by
    exact concrete_pairShift_compatibility R S RI uInv uPush adj I c uStar
      hobj hmap V am k a b E.obj F.obj
  have hchain := congrArg (fun z ↦ e.hom.app EFs ≫ qs.map z ≫ κSS ≫ sh.map ρS) hc
  simp only [Functor.map_comp, Category.assoc] at hchain
  have hpre := (hL.trans hchain.symm).trans hR.symm
  have hi : IsIso kR := by
    change IsIso ((T.tensor.mapIso (Iso.prod ((q.commShiftIso a).app E.obj)
      ((q.commShiftIso b).app F.obj))).hom)
    infer_instance
  have hv : IsIso v := by
    change IsIso ((TS.tensor.mapIso (Iso.prod (e.app E.obj) (e.app F.obj))).hom)
    infer_instance
  apply (cancel_epi (U.map ρs ≫ U.map kR)).1
  apply (cancel_mono (sh.map v)).1
  simpa only [Category.assoc] using hpre

private theorem pullback_coherence :
    ShiftedPullbackCoherence R T S TS uStar
      (shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k) := by
  let D := ShiftedDerivedCategory R
  let A := ShiftedDerivedCategory S
  let U := uStar.mapDerivedCategory
  let m := shiftedExactTensorPullback R T S RI TS uInv uPush adj I c uStar hobj hmap V am k
  unfold ShiftedPullbackCoherence GenericTensorPullbackCoherence
  refine ⟨?_, ?_, ?_⟩
  · let left := isoWhiskerLeft (T.tensor.prod (𝟭 D)) m ≪≫
      isoWhiskerRight (NatIso.prod m (Iso.refl U)) TS.tensor
    let right := isoWhiskerLeft (CategoryTheory.prod.associator D D D)
      (isoWhiskerLeft ((𝟭 D).prod T.tensor) m ≪≫
        isoWhiskerRight (NatIso.prod (Iso.refl U) m) TS.tensor)
    let lhs := isoWhiskerRight (derivedTensorAssociator R T) U ≪≫ right
    let rhs := left ≪≫
      isoWhiskerLeft ((U.prod U).prod U) (derivedTensorAssociator S TS)
    have h : lhs = rhs := by
      apply mixedTernaryIso_ext R
      intro E F G
      apply Iso.ext
      simpa only [lhs, rhs, left, right, Iso.app_hom, Iso.trans_hom,
        NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app,
        whiskerLeft_app, NatIso.prod_hom, NatTrans.prod, Functor.prod_obj,
        Functor.comp_obj, Functor.id_obj, CategoryTheory.prod.associator, Iso.refl_hom,
        NatTrans.id_app, Category.assoc] using
        pullback_associativity_on_models R T S RI TS uInv uPush adj I c uStar
          hobj hmap V am k E F G
    intro X Y Z
    have h' := congrArg (fun z ↦ z.hom.app ((X, Y), Z)) h
    simpa only [lhs, rhs, left, right, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
      NatIso.prod_hom, NatTrans.prod, Functor.prod_obj, Functor.comp_obj, Functor.id_obj,
      CategoryTheory.prod.associator, Iso.refl_hom, NatTrans.id_app, Category.assoc] using h'
  · let swap := CategoryTheory.Prod.swap D D
    let lhs := isoWhiskerRight (derivedTensorSymmetry R T) U ≪≫ isoWhiskerLeft swap m
    let rhs := m ≪≫ isoWhiskerLeft (U.prod U) (derivedTensorSymmetry S TS)
    have h : lhs = rhs := by
      apply mixedBinaryIso_ext R
      intro E F
      apply Iso.ext
      simpa only [lhs, rhs, swap, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
        isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
        Functor.prod_obj, CategoryTheory.Prod.swap_obj, Category.assoc] using
        pullback_symmetry_on_models R T S RI TS uInv uPush adj I c uStar
          hobj hmap V am k E F
    intro X Y
    have h' := congrArg (fun z ↦ z.hom.app (X, Y)) h
    simpa only [lhs, rhs, swap, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.prod_obj,
      CategoryTheory.Prod.swap_obj, Category.assoc] using h'
  · intro a b
    let shift := (shiftFunctor D a).prod (shiftFunctor D b)
    let lhs := isoWhiskerRight (shiftedTensorCanonicalComparison R T a b) U ≪≫
      isoWhiskerLeft T.tensor (U.commShiftIso (a + b)) ≪≫
      isoWhiskerRight m (shiftFunctor A (a + b))
    let rhs := isoWhiskerLeft shift m ≪≫
      isoWhiskerRight (NatIso.prod (U.commShiftIso a) (U.commShiftIso b)) TS.tensor ≪≫
      isoWhiskerLeft (U.prod U) (shiftedTensorCanonicalComparison S TS a b)
    have h : lhs = rhs := by
      apply mixedBinaryIso_ext R
      intro E F
      apply Iso.ext
      simpa only [lhs, rhs, shift, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
        isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
        NatIso.prod_hom, NatTrans.prod, Functor.prod_obj, Functor.comp_obj,
        Category.assoc] using pullback_shift_on_models R T S RI TS uInv uPush adj I c uStar
          hobj hmap V am k a b E F
    intro X Y
    have h' := congrArg (fun z ↦ z.hom.app (X, Y)) h
    simpa only [lhs, rhs, shift, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, NatIso.prod_hom,
      NatTrans.prod, Functor.prod_obj, Functor.comp_obj, Category.assoc] using h'



end PullbackMorphismProofs

/-- The full signed calculus and its exact ringed-topos pullback law.
Source: Stacks 0FPL/0FPM; all ten proof steps of the DAG node are retained below
(blueprint: lem-pur-shifted-tensor-morphism-calculus).
Proof plan:
1. On E[a]^p tensor F[b]^q, move the second shift first. Its sign is (-1)^(bp);
   the two differential coefficients agree as checked in the node's Step 1.
2. The unsigned associator respects the coefficients 1, (-1)^p, (-1)^(p+q).
   Tensor and shifts preserve K-flatness and flat terms, by tensoring an acyclic
   test complex twice and using flatness of sums and tensor products.
3. Descend these maps and the Koszul swap uniquely using
   lem-weil-pbc-site-derived-tensor-descent, variable by variable.
4. Ordinary additive tensor preserves biproduct diagrams; resolving comparisons
   descend this property. Bilinear composition proves both additivity equations.
5. Associativity signs are bp+c(p+q)=cq+(b+c)p. Descend and precompose with f,g,h.
6. Symmetry signs differ by 2bp: bp+(p+a)(q+b) and ab+pq+aq. Descend and use naturality.
7. Flat degree-zero sheaves are K-flat (lem-pc-kflat-closure). Their tensor is flat
   because tensoring by it is the composite of two exact tensor functors. Thus the
   iterated B operations have the specified flat degree-zero sources.
8. For pullback, use the algebraic inverse image and scalar extension in
   def-weil-pbc-algebraic-inverse-image and the pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison. Its associator and swap squares
   agree on locally generating pure tensors.
9. Module pullback preserves sums by lem-weil-pbc-ringed-topoi-module-adjunction.
   Sum the ordinary comparisons over bidegrees. Additivity preserves all differential,
   shift and swap signs; the unsigned associator is preserved by Step 8.
10. lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves resolving models.
   Its unique representative comparison descends the Step 9 diagrams. Exactness
   identifies its derived functor with termwise pullback. The degree-zero comparison
   identifies pulled-back f,g with maps out of uStar P,uStar Q, which are flat.
   Naturality of t gives the pullback clause, including all coherence squares. -/
theorem shiftedTensorMorphismCalculus (a b cshift : ℤ) :
    ShiftedTensorAdditivityClause R T a b ∧
    ShiftedTensorAssociativityClause R T a b cshift ∧
    ShiftedTensorSymmetryClause R T a b ∧
    ShiftedTensorPullbackClause R T S RI TS uInv uPush adj I c uStar hobj hmap V am k a b := by
  obtain ⟨ha, hassoc, hsymm⟩ := shiftedTensorMorphismCalculus_local R T a b cshift
  refine ⟨ha, hassoc, hsymm, ?_⟩
  exact shiftedTensor_pullback_of_coherence R T S RI TS uInv uPush adj I c uStar
    hobj hmap V am k a b
    (shiftedPullback_flat R S RI uInv uPush adj I c uStar hobj hmap)
    (pullback_coherence R T S RI TS uInv uPush adj I c uStar hobj hmap V am k)

end Pullback
end SheafOfModules
