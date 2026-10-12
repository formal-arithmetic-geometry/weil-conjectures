/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Closed immersions of affine schemes into affine space

An affine scheme `X` of finite type over an affine scheme `Spec R` is a closed subscheme of a
relative affine space `𝔸ⁿ_R` over `Spec R`: a surjection `R[x₁, …, xₙ] ⟶ Γ(X)` of `R`-algebras
gives the closed immersion `X ≅ Spec Γ(X) ⟶ Spec R[x₁, …, xₙ] ≅ 𝔸ⁿ_R`.

## Main statements

- `AlgebraicGeometry.AffineSpace.exists_isClosedImmersion_of_isAffine`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

/-- An affine scheme `X` of finite type over `Spec R` admits a closed immersion
`X ⟶ 𝔸ⁿ_R` over `Spec R`, for some `n`. -/
theorem exists_isClosedImmersion_of_isAffine {X : Scheme.{u}} {R : CommRingCat.{u}}
    (π : X ⟶ Spec R) [IsAffine X] [LocallyOfFiniteType π] :
    ∃ (n : ℕ) (i : X ⟶ 𝔸(ULift.{u} (Fin n); Spec R)),
      IsClosedImmersion i ∧ i ≫ 𝔸(ULift.{u} (Fin n); Spec R) ↘ Spec R = π := by
  let : Algebra R Γ(X, ⊤) := (π.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom).toAlgebra
  have : Algebra.FiniteType R Γ(X, ⊤) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appTop @LocallyOfFiniteType π ‹_›)
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  let ψ : MvPolynomial (ULift.{u} (Fin n)) R →ₐ[R] Γ(X, ⊤) :=
    f.comp (MvPolynomial.renameEquiv R Equiv.ulift).toAlgHom
  have hψ : Function.Surjective ψ :=
    hf.comp (MvPolynomial.renameEquiv R Equiv.ulift).surjective
  refine ⟨n, X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    (SpecIso (ULift.{u} (Fin n)) R).inv, ?_, ?_⟩
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ hψ
    infer_instance
  · rw [Category.assoc, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have e : ψ.toRingHom.comp MvPolynomial.C = ((Scheme.ΓSpecIso R).inv ≫ π.appTop).hom := by
      ext a
      exact ψ.commutes a
    rw [e, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id]
    exact Category.comp_id _

end AlgebraicGeometry.AffineSpace
