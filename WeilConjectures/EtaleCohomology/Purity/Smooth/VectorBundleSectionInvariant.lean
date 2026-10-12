/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundle.Trivialization
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace

/-!
# The section invariant of a vector bundle

For a vector bundle `π : E ⟶ B` of rank `r` with zero section `z`
(`AlgebraicGeometry.IsVectorBundleOfRank`), vector-bundle purity (`cor-pur-vector-bundle-purity`)
gives `ω_π ≅ Λ_E(r)[2r]`, and pulling back along the zero section,

`𝒞(π, z) = Lz^* ω_π ≅ Λ_B(r)[2r]`.

This is step 3 of the proof of smooth purity (`sk-thm-smooth-purity`), applied to the normal
bundle of the diagonal.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift_of_isVectorBundleOfRank`:
  vector-bundle purity, `ω_π ≅ Λ_E(r)[2r]`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_twistShift_of_isVectorBundleOfRank`:
  `𝒞(π, z) ≅ Λ_B(r)[2r]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- Blueprint `cor-pur-vector-bundle-purity`: Vector-bundle purity

Let `π : E ⟶ B` be a vector bundle of constant rank `r` with zero section `z`, over a base
separated and locally of finite type over a field on which the exponent of `Λ` is invertible.
Then

`ω_π = Rπ^! Λ_B ≅ Λ_E(r)[2r]`.

In the blueprint the isomorphism is the adjoint of integration against the global trace of the
bundle, glued from the affine-space traces on a trivialising cover; only its existence is
recorded here. -/
-- TODO(unify): the canonical form is the subject of the vector-bundle purity block
-- (`thm-amb-vector-bundle-purity`); this statement is its consequence for `K = Λ_B`.
theorem nonempty_iso_dualizingComplex_twistShift_of_isVectorBundleOfRank
    [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k] (r : ℕ) {E B : Scheme.{u}}
    (p : E ⟶ B) (z : B ⟶ E) [IsVectorBundleOfRank r p z] [HasCompactification p]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) p ≅
      (twistShift Λ E r).obj (constantComplex Λ E)) :=
  sorry

/-- The section invariant of a vector bundle `π : E ⟶ B` of rank `r` with its zero section `z`
is the Tate twist: `𝒞(π, z) = Lz^* ω_π ≅ Lz^* Λ_E(r)[2r] ≅ Λ_B(r)[2r]`, by vector-bundle purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift_of_isVectorBundleOfRank`). -/
theorem nonempty_iso_sectionInvariant_twistShift_of_isVectorBundleOfRank
    [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k] (r : ℕ) {E B : Scheme.{u}}
    (p : E ⟶ B) (z : B ⟶ E) [IsVectorBundleOfRank r p z] [HasCompactification p]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ p z ≅ (twistShift Λ B r).obj (constantComplex Λ B)) := by
  have : HasInvertibleExponent Λ E := .of_hom p
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_twistShift_of_isVectorBundleOfRank Λ r p z aB
  exact ⟨(L((z)^*[ModuleCat.{u + 1} Λ])).mapIso (e ≪≫ twistShiftConstantComplexIso Λ _ _) ≪≫
    leftDerivedUpperStarTateShiftIso Λ _ _ ≪≫ (twistShiftConstantComplexIso Λ B _).symm⟩

end Etale

end AlgebraicGeometry
