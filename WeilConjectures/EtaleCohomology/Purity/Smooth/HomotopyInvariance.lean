/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
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

universe u

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

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- `Λ_X(m)[2m] ≅ Λ_X` for `m = 0`. -/
noncomputable def tateObjectShiftIsoOfEqZero (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m : ℤ) (hm : m = 0) : (tateObject Λ X m)⟦2 * m⟧ ≅ constantComplex Λ X :=
  (shiftFunctorZero' _ (2 * m) (by simp [hm])).app _ ≪≫
    eqToIso (by subst hm; simp [tateObject]) ≪≫ HasTateTwist.twistObjectZeroIso X

/-- `Λ_X(-m)[-2m]` is a left dual of `Λ_X(m)[2m]`. -/
noncomputable def tateObjectShiftExactPairing (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m : ℤ) : ExactPairing ((tateObject Λ X (-m))⟦2 * (-m)⟧) ((tateObject Λ X m)⟦2 * m⟧) :=
  exactPairingOfTensorIso
    (shiftTateObjectAddIso Λ X (-m) m ≪≫ tateObjectShiftIsoOfEqZero Λ X _ (by ring))
    (shiftTateObjectAddIso Λ X m (-m) ≪≫ tateObjectShiftIsoOfEqZero Λ X _ (by ring))

/-- `RHom(Λ(m)[2m], Λ(m)[2m]) ≅ Λ`: the twisting objects are invertible. -/
lemma nonempty_iso_derivedHom_tateObjectShift (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m : ℤ) :
    Nonempty ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op ((tateObject Λ X m)⟦2 * m⟧))).obj
      ((tateObject Λ X m)⟦2 * m⟧) ≅ constantComplex Λ X) := by
  letI := tateObjectShiftExactPairing Λ X m
  exact ⟨ihomObjIsoTensor _ _ _ ≪≫ shiftTateObjectAddIso Λ X (-m) m ≪≫
    tateObjectShiftIsoOfEqZero Λ X _ (by ring)⟩

/-- `RHom(Λ, K) ≅ K`. -/
lemma nonempty_iso_derivedHom_constantComplex {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op (constantComplex Λ X))).obj K ≅ K) :=
  ⟨ihomObjIsoTensor (𝟙_ _) (𝟙_ _) K ≪≫ λ_ K⟩

variable [HasTateTwist.IsNormalized Λ]

/-- Blueprint-free step of homotopy invariance: for relative affine space
`p : 𝔸^d_Y ⟶ Y` over a separated scheme of finite type over a field, `Rp_* Λ ≅ Λ_Y`. -/
theorem nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    Nonempty ((R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y)) ≅ constantComplex Λ Y) := by
  set p := 𝔸(ULift.{u} (Fin d); Y) ↘ Y
  set A := ModuleCat.{u + 1} Λ
  set X := 𝔸(ULift.{u} (Fin d); Y)
  have : HasInvertibleExponent Λ X := .of_hom p
  let M := (twistShift Λ X d).obj (constantComplex Λ X)
  let P := (tateObject Λ X d)⟦2 * (d : ℤ)⟧
  let eM : M ≅ P := (shiftFunctor _ (2 * (d : ℤ))).mapIso (λ_ _)
  obtain ⟨th⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ p M (constantComplex Λ Y)
  obtain ⟨ω⟩ := nonempty_iso_dualizingComplex_affineSpace Λ d Y aY
  obtain ⟨tr⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin Λ d Y
  obtain ⟨hP⟩ := nonempty_iso_derivedHom_tateObjectShift Λ X d
  obtain ⟨hΛ⟩ := nonempty_iso_derivedHom_constantComplex Λ (constantComplex Λ Y)
  -- `RHom(M, Rp^! Λ) ≅ RHom(P, P) ≅ Λ`
  let e₁ : (RHom(X)[A].obj (op M)).obj ((R(p)^![A]).obj (constantComplex Λ Y)) ≅
      constantComplex Λ X :=
    (RHom(X)[A].obj (op M)).mapIso (ω ≪≫ eM) ≪≫ (RHom(X)[A].mapIso eM.symm.op).app P ≪≫ hP
  exact ⟨(R((p)_*[A])).mapIso e₁.symm ≪≫ th ≪≫ (RHom(Y)[A].mapIso tr.symm.op).app _ ≪≫ hΛ⟩

/-- **Homotopy invariance** for relative affine space: the unit `Λ_Y ⟶ Rp_* Λ_{𝔸^d_Y}` is an
isomorphism. -/
theorem isIso_constantComplexUnit_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    IsIso (constantComplexUnit Λ (𝔸(ULift.{u} (Fin d); Y) ↘ Y)) := by
  obtain ⟨ψ⟩ := nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace Λ d Y aY
  let z : Y ⟶ 𝔸(ULift.{u} (Fin d); Y) := AffineSpace.homOfVector (𝟙 Y) 0
  have hz : z ≫ 𝔸(ULift.{u} (Fin d); Y) ↘ Y = 𝟙 Y := AffineSpace.homOfVector_over _ _
  have h := isIso_constantComplexUnit_comp_map_unit Λ _ z hz
  refine isIso_of_comp_eq_id_of_iso _ _ (IsIso.comp_inv_eq.mp ?_ ▸ IsIso.hom_inv_id _) ψ
    (MonoidalCategory.endUnit_comm (C := _root_.DerivedCategory _))
  sorry

end AlgebraicGeometry.Etale
