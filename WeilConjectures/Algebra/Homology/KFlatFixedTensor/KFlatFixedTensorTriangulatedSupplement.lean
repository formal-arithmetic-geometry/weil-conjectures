/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated

/-!
# Exact descent of tensoring with a fixed K-flat complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YM, 06YP and 06YU;
derived.tex, definition-cone and definition-distinguished-triangle;
more-algebra.tex, Tag 0FNH, item-shift-tensor.
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated)

The derived bifunctor and its resolving comparison are the ones already supplied
by site-derived-tensor descent. The presentation packages the existing choices once,
so its dependent comparisons share the same checked data. `derivedTensor_eq_published`
records their equality. All site and coefficient universes remain independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace SheafOfModules.KFlatFixedTensor

section Generic

section CanonicalShift

attribute [local instance 2000] Functor.CommShift₂.commShiftObj
  Functor.CommShift₂.commShiftFlipObj

@[instance_reducible] private def replaceBifunctorShift
    {B E : Type*} [Category* B] [Category* E] [HasShift B ℤ] [HasShift E ℤ]
    [Preadditive E] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (G : B ⥤ B ⥤ E) (s : G.CommShift₂Int)
    (SO : ∀ X, (G.obj X).CommShift ℤ) (SF : ∀ X, (G.flip.obj X).CommShift ℤ)
    (eO : ∀ X, s.commShiftObj X = SO X) (eF : ∀ X, s.commShiftFlipObj X = SF X) :
    G.CommShift₂Int where
  commShiftObj := SO
  commShiftFlipObj := SF
  commShift_map := by
    intro X Y f
    have h := s.commShift_map f
    rw [eO X, eO Y] at h
    exact h
  commShift_flip_map := by
    intro X Y f
    have h := s.commShift_flip_map f
    rw [eF X, eF Y] at h
    exact h
  comm := by
    intro X Y m n
    have h := s.comm X Y m n
    rw [eO, eF, eO, eF] at h
    exact h

@[instance_reducible] private def canonicalLocalizedShift
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    (L : A ⥤ B) (W : MorphismProperty A) [W.ContainsIdentities]
    [L.IsLocalization W] [L.CommShift ℤ]
    (F : A ⥤ A ⥤ E) [F.CommShift₂Int] (G : B ⥤ B ⥤ E)
    [Localization.Lifting₂ L L W W F G] (hsurj : Function.Surjective L.obj)
    (SO : ∀ X, (G.obj X).CommShift ℤ) (SF : ∀ X, (G.flip.obj X).CommShift ℤ)
    (hO : ∀ X, letI := SO (L.obj X)
      NatTrans.CommShift
        (show L ⋙ G.obj (L.obj X) ≅ F.obj X from
          (Localization.Lifting₂.iso L L W W F G).app X).hom ℤ)
    (hF : ∀ X, letI := SF (L.obj X)
      NatTrans.CommShift
        (show L ⋙ G.flip.obj (L.obj X) ≅ F.flip.obj X from
          (Localization.Lifting₂.iso L L W W F.flip G.flip).app X).hom ℤ) :
    G.CommShift₂Int :=
  replaceBifunctorShift G (Functor.commShift₂OfLocalization L L W W F G .int) SO SF
    (canonicalLocalizedShift_obj_eq L W F G hsurj SO hO)
    (canonicalLocalizedShift_flip_eq L W F G hsurj SF hF)

section HomotopyShift
variable {M : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]

@[instance_reducible] private def chainHomotopyBifunctorShift :
    (chainHomotopyBifunctor T).CommShift₂Int :=
  Functor.CommShift₂.postcompInt T.map₂CochainComplex (HomotopyCategory.quotient M (.up ℤ))

@[instance_reducible] private def bifunctorHomotopyLifting :
    Localization.Lifting₂ (HomotopyCategory.quotient M (.up ℤ))
      (HomotopyCategory.quotient M (.up ℤ))
      (HomologicalComplex.homotopyEquivalences M (.up ℤ))
      (HomologicalComplex.homotopyEquivalences M (.up ℤ))
      (chainHomotopyBifunctor T) (homotopyBifunctor T) :=
  ⟨T.whiskeringLeft₂BifunctorMapHomotopyCategoryIso (.up ℤ) (.up ℤ) (.up ℤ)⟩

@[instance_reducible] private def bifunctorHomotopyShift : (homotopyBifunctor T).CommShift₂Int := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  let W := HomologicalComplex.homotopyEquivalences M (.up ℤ)
  let : (chainHomotopyBifunctor T).CommShift₂Int := chainHomotopyBifunctorShift T
  let : Localization.Lifting₂ q q W W (chainHomotopyBifunctor T) (homotopyBifunctor T) :=
    bifunctorHomotopyLifting T
  apply canonicalLocalizedShift q W (chainHomotopyBifunctor T) (homotopyBifunctor T)
    (fun X ↦ X.quotient_obj_surjective) (fun X ↦ inferInstance) (fun X ↦ inferInstance)
  · intro A
    exact inferInstanceAs (NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ)
  · intro A
    exact inferInstanceAs (NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyFlipObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ)

end HomotopyShift

end CanonicalShift

section HomotopyShiftData

attribute [local instance 2000] Functor.CommShift₂.commShiftObj
  Functor.CommShift₂.commShiftFlipObj

end HomotopyShiftData

end Generic

section ShiftKFlat

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

end ShiftKFlat

end SheafOfModules.KFlatFixedTensor
