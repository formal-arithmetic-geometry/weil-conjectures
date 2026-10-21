/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

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

/-- The negative Koszul factor in degrees -1 and 0, at exponent m+1.
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
def ringedNegativeKoszulFactor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) : ringedSiteComplex O :=
  HomologicalComplex.double ((ringedKoszulScalar O b) ^ (m + 1))
    (by decide : (ComplexShape.up ℤ).Rel (-1) 0)

/-- The ordered tensor of negative factors; the empty tensor is O[0].
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
def ringedNegativeKoszul {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) :
    (r : ℕ) → (Fin r → (O.obj ⋙ forget CommRingCat).sections) →
      ℕ → ringedSiteComplex O :=
  fun r ↦ Nat.rec
    (fun _ _ ↦ ringedSiteRingComplex O)
    (fun _ ih b m ↦ ((ringedKoszulTensor O).obj
      (ringedNegativeKoszulFactor O (b 0) m)).obj (ih (fun i ↦ b i.succ) m)) r

/-- Tensoring a complex with the ordered negative Koszul complex at exponent m+1.
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
def ringedNegativeKoszulTensor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) (m : ℕ) : ringedSiteComplex O ⥤ ringedSiteComplex O :=
  (ringedKoszulTensor O).flip.obj
    (ringedNegativeKoszul O r (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m)

/-- A one in a specified degree of the negative two-term factor, zero off its support.
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
def ringedNegativeKoszulFactorBasis {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n : ℤ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      (ringedNegativeKoszulFactor O b m).X n :=
  if h : n = -1 then
    (HomologicalComplex.doubleXIso₀ _ _).inv ≫
      eqToHom (congrArg (ringedNegativeKoszulFactor O b m).X h.symm)
  else if h : n = 0 then
    (HomologicalComplex.doubleXIso₁ _ _ (by decide : (-1 : ℤ) ≠ 0)).inv ≫
      eqToHom (congrArg (ringedNegativeKoszulFactor O b m).X h.symm)
  else 0

/-- The pure tensor with entries one, in the ordered subset coordinate of Q.
The recursion uses the canonical tensor inclusions and the inverse unitor, with no sign
change. The off-degree entries are zero.
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
def ringedNegativeKoszulBasis {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u}) :
    (r : ℕ) → (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) →
      (m : ℕ) → (I : Finset (Fin r)) → (n : ℤ) →
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
        (ringedNegativeKoszul O r b m).X n :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  fun r ↦ Nat.rec
    (fun _ _ _ n ↦ if h : n = 0 then
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
        eqToHom (congrArg (ringedSiteRingComplex O).X h.symm) else 0)
    (fun k ih b m I n ↦
      (MonoidalCategory.leftUnitor
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
      (MonoidalCategory.tensorHom
        (ringedNegativeKoszulFactorBasis O (b 0) m
          (if (0 : Fin (k + 1)) ∈ I then -1 else 0))
        (ih (fun i ↦ b i.succ) m
          (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective k h))
          (n - if (0 : Fin (k + 1)) ∈ I then -1 else 0))) ≫
      CochainComplex.ιMapBifunctor
        (ringedNegativeKoszulFactor O (b 0) m)
        (ringedNegativeKoszul O k (fun i ↦ b i.succ) m)
        (MonoidalCategory.curriedTensor _) (if (0 : Fin (k + 1)) ∈ I then -1 else 0)
        (n - if (0 : Fin (k + 1)) ∈ I then -1 else 0) n (by omega)) r

/-- The canonical inclusion z ↦ z tensor e_I into the total tensor, where every
factor of e_I is one. This fixes the finite-coordinate normalization, including I empty.
Source: Stacks Tag 0A0E (blueprint: def-cbc-signed-koszul-completion-model). -/
def ringedNegativeKoszulSummand {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) (m : ℕ) (K : ringedSiteComplex O)
    (q : ℤ) (I : Finset (Fin r)) :
    K.X (q + I.card) ⟶ ((ringedNegativeKoszulTensor O ρ a m).obj K).X q :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  (MonoidalCategory.rightUnitor (K.X (q + I.card))).inv ≫
    MonoidalCategory.tensorHom (𝟙 _) (ringedNegativeKoszulBasis O r
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I (-(I.card : ℤ))) ≫
    CochainComplex.ιMapBifunctor K
      (ringedNegativeKoszul O r (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m)
      (MonoidalCategory.curriedTensor _) (q + I.card) (-(I.card : ℤ)) q (by omega)

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

/-- The existing global-section Hom scalar action, restricted along the coefficient map.
This transparent wrapper supplies the recorded Hom-module instance explicitly.
Source: Stacks Tags 03DD, 04TT (blueprint: def-cbc-signed-koszul-completion-model). -/
def ringedKoszulCoefficientSMul {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u})
    {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {M N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)}
    (b : A) (f : M ⟶ N) : M ⟶ N :=
  letI := SheafOfModules.homModule O.obj
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property M N
  (ρ b) • f

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
