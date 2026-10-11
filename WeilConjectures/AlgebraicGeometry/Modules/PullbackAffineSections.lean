/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-!
# Global sections of the pullback of a quasi-coherent module along a map of affine schemes

Let `p : Y ⟶ Z` be a morphism of affine schemes and `N` a quasi-coherent `𝒪_Z`-module. Then the
global sections of `p^* N` are `Γ(Y, 𝒪_Y) ⊗_{Γ(Z, 𝒪_Z)} Γ(Z, N)`: the map
`b ⊗ n ↦ b • p^* n` is bijective. This is
`AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_pullback_Spec`, transported along the
isomorphisms `Y ≅ Spec Γ(Y, 𝒪_Y)` and `Z ≅ Spec Γ(Z, 𝒪_Z)`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pullbackΓTensor`: the map
  `Γ(Y, 𝒪_Y) ⊗_{Γ(Z, 𝒪_Z)} Γ(Z, N) → Γ(Y, p^* N)`, `b ⊗ n ↦ b • p^* n`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.bijective_pullbackΓTensor`: it is bijective for `Y`, `Z`
  affine and `N` quasi-coherent.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {Y Z : Scheme.{u}}

/-- The `Γ(Z, 𝒪_Z)`-algebra structure on `Γ(Y, 𝒪_Y)` given by `p : Y ⟶ Z`. -/
noncomputable abbrev appTopAlgebra (p : Y ⟶ Z) : Algebra Γ(Z, ⊤) Γ(Y, ⊤) :=
  p.appTop.hom.toAlgebra

/-- The base change map `Γ(Y, 𝒪_Y) ⊗_{Γ(Z, 𝒪_Z)} Γ(Z, N) → Γ(Y, p^* N)`,
`b ⊗ n ↦ b • p^* n`. -/
noncomputable def pullbackΓTensor (p : Y ⟶ Z) (N : Z.Modules) :
    letI := appTopAlgebra p
    Γ(Y, ⊤) ⊗[Γ(Z, ⊤)] Γ(N, ⊤) →+ Γ((pullback p).obj N, ⊤) :=
  sorry

lemma pullbackΓTensor_tmul (p : Y ⟶ Z) (N : Z.Modules) (b : Γ(Y, ⊤)) (n : Γ(N, ⊤)) :
    letI := appTopAlgebra p
    pullbackΓTensor p N (b ⊗ₜ n) = b • pullbackΓ p N n :=
  sorry

/-- **Base change for quasi-coherent modules along a morphism of affine schemes.** For
`p : Y ⟶ Z` with `Y` and `Z` affine and `N` quasi-coherent, the map
`Γ(Y, 𝒪_Y) ⊗_{Γ(Z, 𝒪_Z)} Γ(Z, N) → Γ(Y, p^* N)`, `b ⊗ n ↦ b • p^* n`, is bijective. -/
theorem bijective_pullbackΓTensor (p : Y ⟶ Z) [IsAffine Y] [IsAffine Z] (N : Z.Modules)
    [N.IsQuasicoherent] : Function.Bijective (pullbackΓTensor p N) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
