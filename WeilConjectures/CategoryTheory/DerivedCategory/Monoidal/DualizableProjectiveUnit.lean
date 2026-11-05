/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Double
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Dualizable objects of `D(C)` when the unit is a finite projective generator of sections

Let `C` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, so that `D(C)` carries the derived tensor product. Suppose that the unit `𝟙` of
`C` is projective and that "global sections" `Hom(𝟙, -)` are finite in the following sense:

* a morphism from `𝟙` to a coproduct factors through a finite subcoproduct
  (`CategoryTheory.UnitFactorsThroughFiniteCoproducts`);
* a morphism from `𝟙` to a tensor product `F ⊗ G` is a finite sum of tensor products of
  morphisms `𝟙 ⟶ F` and `𝟙 ⟶ G` (`CategoryTheory.UnitTensorFinite`).

This is the situation of sheaves of modules on the pro-étale site of an affine weakly contractible
scheme. Then every dualizable object of `D(C)` is isomorphic to a bounded complex of finite
projective objects, that is, of retracts of finite direct sums `𝟙ʳ`
(`DerivedCategory.exists_iso_Q_obj_of_isDualizable`, the forward direction of Stacks 0FPV
in this setting).

## Strategy

1. (`DerivedCategory.exists_retract_of_exactPairing_of_projective_unit`) As over a ring, the
   coevaluation `𝟙 ⟶ K ⊗ N` is a cocycle of degree `0` of `M ⊗ F` for complexes `M`, `F`
   representing `K` and its dual `N` (`F` K-flat with flat terms), since `𝟙` is K-projective.
   By finiteness it is a finite sum of `sᵢ ⊗ tᵢ`, so it comes from the image `L` of a finite sum
   of disk complexes on `𝟙` mapping to `M`; hence `K` is a retract of `Q(L)`, a bounded complex
   whose terms are quotients of `𝟙ʳ`.
2. Consequently `K` is bounded, it has finite Tor amplitude, and if `M` vanishes above `b` the
   top cohomology `Hᵇ(K)` is a quotient of some `𝟙ʳ`.
3. Dualizable objects are closed under cones; one kills the top cohomology by a map
   `𝟙ʳ[-b] ⟶ K` and argues by induction on the length of the Tor amplitude. When the Tor
   amplitude is a single degree, `K = H[-b]` where `H` is a quotient of `𝟙ʳ` with
   `Hom(H, -)` exact, hence a retract of `𝟙ʳ`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- **An elementwise five lemma.** In a preadditive category, consider a commutative ladder
`A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄ ⟶ A₅` over `B₁ ⟶ B₂ ⟶ B₃ ⟶ B₄ ⟶ B₅` whose rows are exact at the
indicated places, in the sense of morphisms from arbitrary objects. If the outer four vertical
maps are isomorphisms, so is the middle one. -/
lemma isIso_of_five_exact {D : Type*} [Category D] [Preadditive D]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : D}
    {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃} {c : A₃ ⟶ A₄} {d : A₄ ⟶ A₅}
    {a' : B₁ ⟶ B₂} {b' : B₂ ⟶ B₃} {c' : B₃ ⟶ B₄} {d' : B₄ ⟶ B₅}
    (γ₁ : A₁ ⟶ B₁) (γ₂ : A₂ ⟶ B₂) (γ₃ : A₃ ⟶ B₃) (γ₄ : A₄ ⟶ B₄) (γ₅ : A₅ ⟶ B₅)
    (h₁ : a ≫ γ₂ = γ₁ ≫ a') (h₂ : b ≫ γ₃ = γ₂ ≫ b') (h₃ : c ≫ γ₄ = γ₃ ≫ c')
    (h₄ : d ≫ γ₅ = γ₄ ≫ d') (hab : a ≫ b = 0) (hcd' : c' ≫ d' = 0)
    (ex₃ : ∀ ⦃W : D⦄ (u : W ⟶ A₃), u ≫ c = 0 → ∃ v, u = v ≫ b)
    (ex₄ : ∀ ⦃W : D⦄ (u : W ⟶ A₄), u ≫ d = 0 → ∃ v, u = v ≫ c)
    (ex₂' : ∀ ⦃W : D⦄ (u : W ⟶ B₂), u ≫ b' = 0 → ∃ v, u = v ≫ a')
    (ex₃' : ∀ ⦃W : D⦄ (u : W ⟶ B₃), u ≫ c' = 0 → ∃ v, u = v ≫ b')
    [IsIso γ₁] [IsIso γ₂] [IsIso γ₄] [IsIso γ₅] : IsIso γ₃ := by
  rw [isIso_iff_yoneda_map_bijective]
  intro W
  refine ⟨fun u₁ u₂ (h : u₁ ≫ γ₃ = u₂ ≫ γ₃) ↦ ?_, fun u' ↦ ?_⟩
  · rw [← sub_eq_zero]
    have hu : (u₁ - u₂) ≫ γ₃ = 0 := by rw [Preadditive.sub_comp, h, sub_self]
    have h1 : (u₁ - u₂) ≫ c = 0 := by
      rw [← cancel_mono γ₄, Category.assoc, h₃, reassoc_of% hu, zero_comp, zero_comp]
    obtain ⟨v, hv⟩ := ex₃ _ h1
    have h2 : (v ≫ γ₂) ≫ b' = 0 := by
      rw [Category.assoc, ← h₂, ← Category.assoc, ← hv, hu]
    obtain ⟨w', hw'⟩ := ex₂' _ h2
    have : v = (w' ≫ inv γ₁) ≫ a := by
      rw [← cancel_mono γ₂, hw', Category.assoc, Category.assoc, h₁, IsIso.inv_hom_id_assoc]
    rw [hv, this, Category.assoc, hab, comp_zero]
  · have hy : (u' ≫ c' ≫ inv γ₄) ≫ d = 0 := by
      rw [← cancel_mono γ₅]
      simp only [Category.assoc, h₄, IsIso.inv_hom_id_assoc, hcd', comp_zero, zero_comp]
    obtain ⟨u, hu⟩ := ex₄ _ hy
    have h3 : (u' - u ≫ γ₃) ≫ c' = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← h₃, ← Category.assoc, ← hu]
      simp
    obtain ⟨v', hv'⟩ := ex₃' _ h3
    refine ⟨u + (v' ≫ inv γ₂) ≫ b, ?_⟩
    change (u + (v' ≫ inv γ₂) ≫ b) ≫ γ₃ = u'
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, h₂, IsIso.inv_hom_id_assoc, ← hv']
    abel

namespace MonoidalClosed

variable {D : Type*} [Category D] [MonoidalCategory D] [MonoidalClosed D]

/-- The comparison `[X, 𝟙] ⊗ Z ⟶ [X, Z]` is natural in `X`. -/
lemma ihomUnitTensorToIhom_pre {X X' : D} (f : X ⟶ X') (Z : D) :
    ihomUnitTensorToIhom X' Z ≫ (pre f).app Z =
      (pre f).app (𝟙_ D) ▷ Z ≫ ihomUnitTensorToIhom X Z := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev,
    whiskerLeft_ihomUnitTensorToIhom_ev, whisker_exchange_assoc,
    whiskerLeft_ihomUnitTensorToIhom_ev, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc,
    associator_inv_naturality_left_assoc]

end MonoidalClosed

end CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] Abelian.hasFiniteBiproducts

end DerivedCategory

namespace DerivedCategory

open Pretriangulated MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

/-- A shift of a dualizable object of `D(C)` is dualizable: `X⟦n⟧ ≅ X ⊗ 𝟙⟦n⟧`, and `𝟙⟦n⟧` has
tensor inverse `𝟙⟦-n⟧`. -/
lemma isDualizable_shift {X : DerivedCategory C} (hX : IsDualizable X) (n : ℤ) :
    IsDualizable (X⟦n⟧) := by
  let U := 𝟙_ (DerivedCategory C)
  have hU : IsDualizable (U⟦n⟧) := isDualizable_of_tensorIso (Y := U⟦-n⟧)
    (shiftTensorShiftIso (X := U) (Y := U) (a := n) (b := -n) ≪≫ (shiftFunctor _ _).mapIso (λ_ U) ≪≫
      eqToIso (by rw [add_neg_cancel]) ≪≫ (shiftFunctorZero _ ℤ).app U)
    (shiftTensorShiftIso (X := U) (Y := U) (a := -n) (b := n) ≪≫ (shiftFunctor _ _).mapIso (λ_ U) ≪≫
      eqToIso (by rw [neg_add_cancel]) ≪≫ (shiftFunctorZero _ ℤ).app U)
  have hX0 : IsDualizable (X⟦(0 : ℤ)⟧) := IsDualizable.of_iso ((shiftFunctorZero _ ℤ).app X).symm hX
  exact IsDualizable.of_iso (shiftTensorShiftIso (X := X) (Y := U) (a := 0) (b := n) ≪≫
    (shiftFunctor _ _).mapIso (ρ_ X) ≪≫
    eqToIso (by rw [zero_add])) (hX0.tensorObj hU)

/-- **Dualizable objects are closed under cones.** If two vertices `T.obj₁` and `T.obj₂` of a
distinguished triangle of `D(C)` are dualizable, so is the third. For any `Z`, both
`X ↦ [X, 𝟙] ⊗ Z` and `X ↦ [X, Z]` carry distinguished triangles to distinguished triangles, and
the comparison `[X, 𝟙] ⊗ Z ⟶ [X, Z]`, natural in `X`, is an isomorphism for dualizable `X`; the
five lemma applies to the rotations of `T`. -/
theorem isDualizable_obj₃_of_distTriang (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (h₁ : IsDualizable T.obj₁) (h₂ : IsDualizable T.obj₂) :
    IsDualizable T.obj₃ := by
  obtain ⟨_⟩ := nonempty_braidedCategory C
  rw [isDualizable_iff_isIso_ihomUnitTensorToIhom]
  have hiso {X : DerivedCategory C} (hX : IsDualizable X) (Z : DerivedCategory C) :
      IsIso (ihomUnitTensorToIhom X Z) := by
    obtain ⟨_⟩ := hX
    let := BraidedCategory.exactPairing_swap X Xᘁ
    exact isIso_ihomUnitTensorToIhom Xᘁ X Z
  set Z := T.obj₃
  have hT₁ := rot_of_distTriang _ hT
  have hT₂ := rot_of_distTriang _ hT₁
  obtain ⟨k₀, hk₀⟩ := exists_distinguished_ihom_pre T hT (𝟙_ _)
  obtain ⟨k₁, hk₁⟩ := exists_distinguished_ihom_pre _ hT₁ (𝟙_ _)
  obtain ⟨k₂, hk₂⟩ := exists_distinguished_ihom_pre _ hT₂ (𝟙_ _)
  have hF₀ := (tensorRight Z).map_distinguished _ hk₀
  have hF₁ := (tensorRight Z).map_distinguished _ hk₁
  have hF₂ := (tensorRight Z).map_distinguished _ hk₂
  obtain ⟨l₀, hl₀⟩ := exists_distinguished_ihom_pre T hT Z
  obtain ⟨l₁, hl₁⟩ := exists_distinguished_ihom_pre _ hT₁ Z
  obtain ⟨l₂, hl₂⟩ := exists_distinguished_ihom_pre _ hT₂ Z
  have : IsIso (ihomUnitTensorToIhom T.rotate.rotate.obj₂ Z) := hiso (isDualizable_shift h₁ 1) Z
  have : IsIso (ihomUnitTensorToIhom T.rotate.rotate.obj₃ Z) := hiso (isDualizable_shift h₂ 1) Z
  have := hiso h₁ Z
  have := hiso h₂ Z
  exact isIso_of_five_exact (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z)
    (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z)
    (ihomUnitTensorToIhom_pre _ _).symm (ihomUnitTensorToIhom_pre _ _).symm
    (ihomUnitTensorToIhom_pre _ _).symm (ihomUnitTensorToIhom_pre _ _).symm
    (comp_distTriang_mor_zero₁₂ _ hF₂) (comp_distTriang_mor_zero₁₂ _ hl₀)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hF₁ u hu)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hF₀ u hu)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hl₂ u hu)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hl₁ u hu)

end DerivedCategory

namespace CategoryTheory

open Limits

section FinProj

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C]

/-- The biproduct of copies of an object `X` indexed by a sum of finite types is the binary
biproduct of the two partial biproducts. -/
noncomputable def biprodBiproductConstIso (X : C) (ι κ : Type) [Finite ι] [Finite κ] :
    (⨁ fun _ : ι ↦ X) ⊞ (⨁ fun _ : κ ↦ X) ≅ ⨁ fun _ : ι ⊕ κ ↦ X where
  hom := biprod.desc (biproduct.desc fun i ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ X) (Sum.inl i))
    (biproduct.desc fun k ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ X) (Sum.inr k))
  inv := biproduct.desc fun s ↦ Sum.elim (fun i ↦ biproduct.ι (fun _ : ι ↦ X) i ≫ biprod.inl)
    (fun k ↦ biproduct.ι (fun _ : κ ↦ X) k ≫ biprod.inr) s
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro j <;> simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    rintro (i | k) <;> simp

/-- The biproduct of `r + s` copies of `X` is the binary biproduct of `r` and `s` copies. -/
noncomputable def biprodBiproductFinIso (X : C) (r s : ℕ) :
    (⨁ fun _ : Fin r ↦ X) ⊞ (⨁ fun _ : Fin s ↦ X) ≅ ⨁ fun _ : Fin (r + s) ↦ X :=
  biprodBiproductConstIso X (Fin r) (Fin s) ≪≫
    biproduct.whiskerEquiv (f := fun _ : Fin r ⊕ Fin s ↦ X) (g := fun _ : Fin (r + s) ↦ X)
      finSumFinEquiv (fun _ ↦ Iso.refl _)

variable [MonoidalCategory C]

lemma isDualizable_biproduct_unit [MonoidalPreadditive C] (r : ℕ) :
    IsDualizable (⨁ fun _ : Fin r ↦ 𝟙_ C) := by
  induction r with
  | zero =>
    refine CategoryTheory.IsZero.isDualizable
      ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ ?_))
    exact fun i ↦ i.elim0
  | succ r ih =>
    exact IsDualizable.of_iso (biprodBiproductFinIso _ r 1)
      (IsDualizable.biprod ih (IsDualizable.of_iso (biproductUniqueIso _).symm isDualizable_unit))

end FinProj

end CategoryTheory
