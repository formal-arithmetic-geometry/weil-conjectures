/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel

/-!
# The explicit signed Koszul completion model

Source: Stacks Project, algebraization.tex, Tag 0A0E, and the finite-coordinate calculation
in lem-cbc-exact-linear-koszul-fiber (blueprint: def-cbc-signed-koszul-completion-model).

The negative Koszul factors are actual two-term complexes and their ordered tensor uses
`ringedKoszulTensor`, hence `CochainComplex.mapBifunctor` and its total-tensor signs.
The model structure records products by their universal property and the fibre by its
specified two coordinates. No object is selected from an unspecified existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CategoryTheory

/-- A signed Koszul model, specified by its finite coordinates, product universal property,
shift, fibre differential and coaugmentation. Index m means the positive exponent m+1.
The coefficient of an erased index i is (-1)^(q+|J|) times the sign counting earlier factors.
All casts are equality transports between the displayed degrees; no choice of cone occurs.
Source: Stacks Tag 0A0E and the explicit calculation in lem-cbc-exact-linear-koszul-fiber
(blueprint: def-cbc-signed-koszul-completion-model). -/
structure SignedKoszulCompletionModel (A : Type z) [CommRing A]
    (E : Type u) [Category.{v} E] [Preadditive E]
    [HasFiniteBiproducts E] [HasBinaryBiproducts E]
    (σ : ∀ {X Y : E}, A → (X ⟶ Y) → (X ⟶ Y)) {r : ℕ} (a : Fin r → A)
    (T : ℕ → CochainComplex E ℤ ⥤ CochainComplex E ℤ) where
  /-- The canonical multiplication coordinates of the total tensor. -/
  coordinates : ∀ (m : ℕ) (K : CochainComplex E ℤ) (q : ℤ),
    ((T m).obj K).X q ≅ ⨁ fun I : Finset (Fin r) ↦ K.X (q + I.card)
  /-- The signed total differential on every pair of finite summands. -/
  differential : ∀ (m : ℕ) (K : CochainComplex E ℤ) (q : ℤ)
      (I L : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates m K q).inv ≫
        ((T m).obj K).d q (q + 1) ≫ (coordinates m K (q + 1)).hom ≫
          biproduct.π _ L =
      (if I = L then K.d (q + I.card) ((q + 1) + L.card) else 0) +
      (if h : q + (I.card : ℤ) = (q + 1) + (L.card : ℤ) then
        σ (∑ i ∈ I, if I.erase i = L then
          (if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
            (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1) else 0)
              (K.XIsoOfEq h).hom else 0)
  /-- A coefficient chain map acts diagonally in the finite coordinates. -/
  map_coordinates : ∀ (m : ℕ) {K L : CochainComplex E ℤ} (f : K ⟶ L)
      (q : ℤ) (I P : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates m K q).inv ≫ ((T m).map f).f q ≫
        (coordinates m L q).hom ≫ biproduct.π _ P =
      if h : I = P then f.f (q + I.card) ≫
        (L.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
      else 0
  /-- The inverse transition T_(m+2) to T_(m+1). -/
  step : ∀ m : ℕ, T (m + 1) ⟶ T m
  /-- Its I coordinate is multiplication by the product of the scalars in I. -/
  step_coordinates : ∀ (m : ℕ) (K : CochainComplex E ℤ) (q : ℤ)
      (I L : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates (m + 1) K q).inv ≫ ((step m).app K).f q ≫
        (coordinates m K q).hom ≫ biproduct.π _ L =
      if h : I = L then σ (∏ i ∈ I, a i)
        (K.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
      else 0
  /-- The inclusion into the empty-subset coordinate. -/
  inclusion : ∀ m : ℕ, 𝟭 (CochainComplex E ℤ) ⟶ T m
  /-- The inclusion has identity empty coordinate and zero other coordinates. -/
  inclusion_coordinates : ∀ (m : ℕ) (K : CochainComplex E ℤ) (q : ℤ)
      (I : Finset (Fin r)),
    ((inclusion m).app K).f q ≫ (coordinates m K q).hom ≫ biproduct.π _ I =
      if h : q = q + (I.card : ℤ) then (K.XIsoOfEq h).hom else 0
  /-- The product of the tower, in complexes. -/
  product : CochainComplex E ℤ ⥤ CochainComplex E ℤ
  /-- Its projections. -/
  projection : ∀ m : ℕ, product ⟶ T m
  /-- The projections exhibit a categorical product, including its differential. -/
  isProduct : ∀ K : CochainComplex E ℤ,
    IsLimit (Fan.mk (product.obj K) (fun m ↦ (projection m).app K))
  /-- The transition shift on this product. -/
  shift : product ⟶ product
  /-- The mth projection of the shift is transition after the next projection. -/
  shift_projection : ∀ (m : ℕ) (K : CochainComplex E ℤ),
    shift.app K ≫ (projection m).app K = (projection (m + 1)).app K ≫ (step m).app K
  /-- The diagonal map with components the degree-zero inclusions. -/
  diagonal : 𝟭 (CochainComplex E ℤ) ⟶ product
  /-- The diagonal is characterized by these projections. -/
  diagonal_projection : ∀ (m : ℕ) (K : CochainComplex E ℤ),
    diagonal.app K ≫ (projection m).app K = (inclusion m).app K
  /-- The signed fibre functor. -/
  fibre : CochainComplex E ℤ ⥤ CochainComplex E ℤ
  /-- Its two specified coordinates in degree q. -/
  fibreCoordinates : ∀ (K : CochainComplex E ℤ) (q : ℤ),
    (fibre.obj K).X q ≅ (product.obj K).X q ⊞ (product.obj K).X (q - 1)
  /-- The differential is exactly (dx, (1-s)x-dy). -/
  fibre_differential : ∀ (K : CochainComplex E ℤ) (q : ℤ),
    (fibreCoordinates K q).inv ≫ (fibre.obj K).d q (q + 1) ≫
        (fibreCoordinates K (q + 1)).hom =
      biprod.lift (biprod.fst ≫ (product.obj K).d q (q + 1))
        (biprod.fst ≫ (𝟙 _ - (shift.app K).f q) ≫
            ((product.obj K).XIsoOfEq (Int.add_sub_cancel q 1).symm).hom -
          biprod.snd ≫ (product.obj K).d (q - 1) ((q + 1) - 1))
  /-- Maps of fibres are diagonal maps of products. -/
  fibre_map : ∀ {K L : CochainComplex E ℤ} (f : K ⟶ L) (q : ℤ),
    (fibreCoordinates K q).inv ≫ (fibre.map f).f q ≫ (fibreCoordinates L q).hom =
      biprod.map ((product.map f).f q) ((product.map f).f (q - 1))
  /-- The coaugmentation into the fibre. -/
  unit : 𝟭 (CochainComplex E ℤ) ⟶ fibre
  /-- Its two coordinates are the diagonal inclusion and zero. -/
  unit_coordinates : ∀ (K : CochainComplex E ℤ) (q : ℤ),
    (unit.app K).f q ≫ (fibreCoordinates K q).hom =
      biprod.lift ((diagonal.app K).f q) 0

/-- The preceding model for sheaves, using the existing global-section coefficient action
and the actual ordered total tensor with negative Koszul factors.
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
abbrev RingedSignedKoszulCompletionModelBase {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) :=
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  SignedKoszulCompletionModel A
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (fun {_ _} b f ↦ ringedKoszulCoefficientSMul O ρ b f) a (ringedNegativeKoszulTensor O ρ a)

/-- The signed sheaf model with its coordinates normalized by actual tensor inclusions.
Thus its unit is c ↦ ((c tensor 1)_m,0), not an independently chosen coaugmentation.
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
structure RingedSignedKoszulCompletionModel {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) where
  /-- The explicitly signed model. -/
  model : RingedSignedKoszulCompletionModelBase O ρ a
  /-- The I inclusion is the pure tensor with ones in the same ordered factors. -/
  normalization : ∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)),
    biproduct.ι _ I ≫ (model.coordinates m K q).inv =
      ringedNegativeKoszulSummand O ρ a m K q I

end CategoryTheory
