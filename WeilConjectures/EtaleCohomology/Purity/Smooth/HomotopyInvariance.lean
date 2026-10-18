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
    (m : ℤ) (hm : m = 0) : (tateObject Λ X m)⟦2 * m⟧ ≅ constantComplex Λ X := by
  subst hm
  exact (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).app _ ≪≫ HasTateTwist.twistObjectZeroIso X

/-- test -/
noncomputable def tateObjectShiftTensorIso (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m m' : ℤ) (h : m + m' = 0) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X m)⟦2 * m⟧)).obj
        ((tateObject Λ X m')⟦2 * m'⟧) ≅ constantComplex Λ X :=
  shiftTateObjectAddIso Λ X m m' ≪≫ tateObjectShiftIsoOfEqZero Λ X _ h

/-- `Λ_X(-m)[-2m]` is a left dual of `Λ_X(m)[2m]`. -/
noncomputable def tateObjectShiftExactPairing (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m : ℤ) : ExactPairing ((tateObject Λ X (-m))⟦2 * (-m)⟧) ((tateObject Λ X m)⟦2 * m⟧) :=
  exactPairingOfTensorIso (tateObjectShiftTensorIso Λ X (-m) m (by ring))
    (tateObjectShiftTensorIso Λ X m (-m) (by ring))

end AlgebraicGeometry.Etale
