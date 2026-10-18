/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# Homotopy invariance of étale cohomology for affine space

For the projection `p : 𝔸^d_Y ⟶ Y` of relative affine space over a separated scheme of finite
type over a field, on which the exponent of `Λ` is invertible, the unit `Λ_Y ⟶ Rp_* Λ_{𝔸^d_Y}` is
an isomorphism (`AlgebraicGeometry.Etale.isIso_constantComplexUnit_affineSpace`).

The proof is by duality. The tensor–Hom exchange
`Rp_* RHom(M, Rp^! Λ_Y) ≅ RHom(Rp_! M, Λ_Y)`, at `M = Λ(d)[2d]`, together with affine-space
purity `Rp^! Λ_Y ≅ Λ(d)[2d]` and the affine-space trace `Rp_! Λ(d)[2d] ≅ Λ_Y`, gives some
isomorphism `Rp_* Λ ≅ Λ_Y` (`RHom(M, M) ≅ Λ` as `M` is invertible). The unit has a left
inverse, restriction along the zero section, and the endomorphisms of `Λ_Y` commute (they are
endomorphisms of the monoidal unit), so the unit is itself an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- The endomorphisms of the monoidal unit commute (Eckmann–Hilton). -/
lemma MonoidalCategory.endUnit_comm {C : Type*} [Category C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have h₁ : 𝟙_ C ◁ g = (λ_ (𝟙_ C)).hom ≫ g ≫ (λ_ (𝟙_ C)).inv := by
    rw [← leftUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have h₂ : f ▷ 𝟙_ C = (λ_ (𝟙_ C)).hom ≫ f ≫ (λ_ (𝟙_ C)).inv := by
    rw [unitors_equal, unitors_inv_equal, ← rightUnitor_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h := whisker_exchange f g
  rw [h₁, h₂] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc, cancel_epi] at h
  simpa using h.symm

/-- A morphism `u : A ⟶ B` with a left inverse is an isomorphism if `B ≅ A` and the
endomorphisms of `A` commute. -/
lemma isIso_of_comp_eq_id_of_iso {C : Type*} [Category C] {A B : C} (u : A ⟶ B) (r : B ⟶ A)
    (hur : u ≫ r = 𝟙 A) (ψ : B ≅ A) (hcomm : ∀ f g : A ⟶ A, f ≫ g = g ≫ f) : IsIso u := by
  have h₁ : (u ≫ ψ.hom) ≫ (ψ.inv ≫ r) = 𝟙 A := by simp [hur]
  have h₂ : (ψ.inv ≫ r) ≫ (u ≫ ψ.hom) = 𝟙 A := by rw [← hcomm, h₁]
  have : IsIso (u ≫ ψ.hom) := ⟨⟨_, h₁, h₂⟩⟩
  have : u = (u ≫ ψ.hom) ≫ ψ.inv := by simp
  rw [this]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.Etale

section Generic

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

attribute [local instance] derivedBraidedCategory

/-- `RHom(Λ, K) ≅ K`. -/
lemma nonempty_iso_derivedHom_unit (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((RHom(X)[A].obj (op (𝟙_ _))).obj K ≅ K) :=
  ⟨MonoidalClosed.ihomObjIsoTensor (𝟙_ _) (𝟙_ _) K ≪≫ λ_ K⟩

/-- `RHom(T, T) ≅ Λ` for an invertible `T`. -/
lemma nonempty_iso_derivedHom_self_of_isInvertible
    {T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hT : IsInvertible T) :
    Nonempty ((RHom(X)[A].obj (op T)).obj T ≅ 𝟙_ _) := by
  have := MonoidalClosed.isIso_ihomUnitToIhomTensor (𝟙_ _) hT
  obtain ⟨e⟩ := nonempty_iso_derivedHom_unit (A := A) (X := X) (𝟙_ _)
  exact ⟨(MonoidalClosed.internalHom.flip.obj T).mapIso (λ_ T).op ≪≫
    (asIso (MonoidalClosed.ihomUnitToIhomTensor (𝟙_ _) T)).symm ≪≫ e⟩

/-- The endomorphisms of `Λ_X` commute. -/
lemma endUnit_comm_derivedCategory
    (f g : 𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) ⟶ 𝟙_ _) :
    f ≫ g = g ≫ f :=
  MonoidalCategory.endUnit_comm f g

end Generic

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

/-- `RHom(Λ(m)[2m], Λ(m)[2m]) ≅ Λ`: the twisting objects are invertible. -/
lemma nonempty_iso_derivedHom_tateObjectShift (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (d : ℕ) :
    Nonempty ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op ((tateObject Λ X d)⟦(2 * d : ℤ)⟧))).obj
      ((tateObject Λ X d)⟦(2 * d : ℤ)⟧) ≅ constantComplex Λ X) :=
  nonempty_iso_derivedHom_self_of_isInvertible (isInvertible_tateObject_shift Λ X d)

variable [Finite Λ] [HasTateTwist.IsNormalized Λ]

/-- For relative affine space `p : 𝔸^d_Y ⟶ Y` over a separated scheme of finite type over a
field, `Rp_* Λ ≅ Λ_Y`: by the tensor–Hom exchange,
`Rp_* RHom(Λ(d)[2d], Rp^! Λ) ≅ RHom(Rp_! Λ(d)[2d], Λ)`, where `Rp^! Λ ≅ Λ(d)[2d]` (purity) and
`Rp_! Λ(d)[2d] ≅ Λ` (the affine-space trace). -/
theorem nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    Nonempty ((R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y)) ≅ constantComplex Λ Y) := by
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); Y) := .of_hom (𝔸(ULift.{u} (Fin d); Y) ↘ Y)
  obtain ⟨th⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ (𝔸(ULift.{u} (Fin d); Y) ↘ Y)
    ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y)))
    (constantComplex Λ Y)
  obtain ⟨ω⟩ := nonempty_iso_dualizingComplex_affineSpace Λ d Y aY
  obtain ⟨tr⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin Λ d Y
  obtain ⟨hP⟩ := nonempty_iso_derivedHom_tateObjectShift Λ 𝔸(ULift.{u} (Fin d); Y) d
  obtain ⟨hΛ⟩ := nonempty_iso_derivedHom_unit (A := ModuleCat.{u + 1} Λ)
    (𝟙_ _ : _root_.DerivedCategory
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  let eM : (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))
      ≅ (tateObject Λ 𝔸(ULift.{u} (Fin d); Y) d)⟦(2 * d : ℤ)⟧ :=
    (shiftFunctor _ (2 * (d : ℤ))).mapIso (derivedTensorLeftUnitor _ _ _)
  let e₁ := (RHom(_)[ModuleCat.{u + 1} Λ].obj (op ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))))).mapIso (ω ≪≫ eM) ≪≫
    (RHom(_)[ModuleCat.{u + 1} Λ].mapIso eM.symm.op).app _ ≪≫ hP
  exact ⟨(R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso e₁.symm ≪≫ th ≪≫
    (RHom(Y)[ModuleCat.{u + 1} Λ].mapIso tr.symm.op).app _ ≪≫ hΛ⟩

/-- **Homotopy invariance** for relative affine space: over a separated scheme `Y` of finite
type over a field, the unit `Λ_Y ⟶ Rp_* Λ_{𝔸^d_Y}` is an isomorphism. It has a left inverse,
restriction along the zero section, and `Rp_* Λ ≅ Λ_Y`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace`);
the endomorphisms of `Λ_Y` commute, so a morphism `Λ_Y ⟶ Rp_* Λ` with a left inverse is an
isomorphism. -/
theorem isIso_constantComplexUnit_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    IsIso (constantComplexUnit Λ (𝔸(ULift.{u} (Fin d); Y) ↘ Y)) := by
  obtain ⟨ψ⟩ := nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace Λ d Y aY
  let z : Y ⟶ 𝔸(ULift.{u} (Fin d); Y) := AffineSpace.homOfVector (𝟙 Y) 0
  have hz : z ≫ 𝔸(ULift.{u} (Fin d); Y) ↘ Y = 𝟙 Y := AffineSpace.homOfVector_over _ _
  have := isIso_constantComplexUnit_comp_map_unit Λ _ z hz
  let w := (R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).map
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) z).unit.app
      (constantComplex Λ _))
  refine isIso_of_comp_eq_id_of_iso _ (w ≫ inv (constantComplexUnit Λ _ ≫ w)) ?_ ψ
    endUnit_comm_derivedCategory
  rw [← Category.assoc, IsIso.hom_inv_id]

end AlgebraicGeometry.Etale
