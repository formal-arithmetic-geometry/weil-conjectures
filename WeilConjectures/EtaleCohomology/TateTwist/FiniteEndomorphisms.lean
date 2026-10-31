/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine

/-!
# Endomorphisms of the Tate twists over a connected scheme are finite

Let `Λ` be a finite commutative ring and `X` a connected scheme. The endomorphisms of the
constant complex `Λ_X` in `D(X_ét, Λ)` are the global sections of the constant sheaf, which is
`Λ` (`AlgebraicGeometry.Etale.finite_endomorphisms_constantComplex`). Tensoring with an object
having a tensor inverse is injective on morphisms
(`CategoryTheory.MonoidalCategory.whiskerRight_injective_of_tensorIsoUnit`), so every invertible
object, for instance every Tate twist `Λ_X(m)`, has finitely many endomorphisms
(`AlgebraicGeometry.Etale.finite_endomorphisms_tateObject`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- Whiskering on the right with an object `M` which has a left tensor inverse `L`,
`M ⊗ L ≅ 𝟙`, is injective on morphisms. -/
lemma whiskerRight_injective_of_tensorIsoUnit {M L : C} (e : M ⊗ L ≅ 𝟙_ C) {A B : C} :
    Function.Injective (fun φ : A ⟶ B ↦ φ ▷ M) := by
  intro φ ψ h
  have h₁ : φ ▷ (M ⊗ L) = ψ ▷ (M ⊗ L) := by
    simp only at h
    rw [whiskerRight_tensor, whiskerRight_tensor, h]
  have h₂ (χ : A ⟶ B) : χ = (ρ_ A).inv ≫ A ◁ e.inv ≫ χ ▷ (M ⊗ L) ≫ B ◁ e.hom ≫ (ρ_ B).hom := by
    rw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, ← rightUnitor_inv_naturality_assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [h₂ φ, h₂ ψ, h₁]

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})

/-- **The endomorphisms of the constant complex over a connected scheme are finite**: they are
the global sections of the constant sheaf `Λ_X`, which is `Λ`. -/
lemma finite_endomorphisms_constantComplex [ConnectedSpace X] :
    Finite (constantComplex Λ X ⟶ constantComplex Λ X) := by
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  let hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  have hb := bijective_constantSheafAdj_unit_app (X := X) (Λ := Λ) (M := ModuleCat.of Λ Λ) hT
  have hΓ := @Finite.of_surjective _ _ (inferInstanceAs (Finite Λ)) _ hb.2
  have h₁ := @Finite.of_injective (ModuleCat.of Λ Λ ⟶ ((sheafSections X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X) _))).obj F) _ hΓ
    (fun g ↦ g.hom (1 : Λ))
    fun g g' h ↦ ModuleCat.hom_ext (LinearMap.ext_ring h)
  have h₂ : Finite (F ⟶ F) := Finite.of_equiv _ (adj.homEquiv _ _).symm
  let e := constantComplexIsoSingleFunctorConstantSheaf Λ X
  exact Finite.of_equiv _ ((Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor _ 0))
    |>.homEquiv.trans (e.homCongr e).symm)

variable {Λ X} in
/-- **An invertible object of `D(X_ét, Λ)` over a connected scheme has finitely many
endomorphisms**: `φ ↦ φ ⊗ M` embeds them into the endomorphisms of `Λ_X ≅ L ⊗ M`. -/
lemma finite_endomorphisms_of_isInvertible [ConnectedSpace X]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.isInvertible Λ X L) : Finite (L ⟶ L) := by
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := hL
  have := finite_endomorphisms_constantComplex Λ X
  exact Finite.of_injective (fun φ : L ⟶ L ↦ e₁.inv ≫ φ ▷ M ≫ e₁.hom) fun φ ψ h ↦
    whiskerRight_injective_of_tensorIsoUnit (A := L) (B := L) e₂ (by simpa using h)

/-- **The Tate twists over a connected scheme have finitely many endomorphisms.** -/
lemma finite_endomorphisms_tateObject [HasTateTwist Λ] [HasInvertibleExponent Λ X]
    [ConnectedSpace X] (m : ℤ) : Finite (tateObject Λ X m ⟶ tateObject Λ X m) :=
  finite_endomorphisms_of_isInvertible (HasTateTwist.isInvertible_twistObject X m)

end AlgebraicGeometry.Etale
