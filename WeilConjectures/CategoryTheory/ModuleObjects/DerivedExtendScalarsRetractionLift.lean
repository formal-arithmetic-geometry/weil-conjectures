/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransitionComplex
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangulated
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.RetractionLift

/-!
# Lifting compatible retractions from the reductions modulo `mⁿ⁺¹`

Let `R` be a commutative algebra object of a closed symmetric monoidal Grothendieck abelian
category `C`, `m` an integer and `φₙ : R ⟶ Sₙ` morphisms of commutative algebra objects such that
`0 ⟶ R --mⁿ⁺¹--> R --φₙ--> Sₙ ⟶ 0` is short exact, with transitions `ψₙ : Sₙ₊₁ ⟶ Sₙ`,
`φₙ₊₁ ≫ ψₙ = φₙ` (the case of interest is `R = 𝒪_E`, `m = ℓ`, `Sₙ = 𝒪_E/ℓⁿ⁺¹`). Let
`i : A ⟶ B` be a morphism of `D(Mod_R(C))` whose source `A` is complete with respect to `m`
(every morphism to `A` from an object on which `m` acts invertibly vanishes; for instance a
derived complete `𝒪_E`-complex).

* `Mod.isSplitMono_of_isCenterComplete_of_retractions`: if the reductions `Sₙ ⊗ᴸ_R i` admit
  morphisms `sₙ : Sₙ ⊗ᴸ_R B ⟶ Sₙ ⊗ᴸ_R A` which are compatible with reduction (the reduction
  `Sₙ ⊗ᴸ_{Sₙ₊₁} sₙ₊₁` of `sₙ₊₁` is `sₙ`, `Mod.derivedExtendScalarsReduction`) and `s₀` is a
  retraction of `S₀ ⊗ᴸ_R i`, then `i` is a split monomorphism.
* `Mod.isSplitMono_of_isCenterComplete_of_unique_retractions`: the compatibility holds as soon as
  each `Sₙ ⊗ᴸ_R i` has a unique retraction with some property `Pₙ` which is preserved by reduction
  (for torsion nearby cycles, the retraction which is invariant under the Galois action).

## Proof

Write `ηₙ : K ⟶ Sₙ ⊗ᴸ_R K` for the units, `tₙ` for the transitions
(`Mod.derivedReductionTransition`) and `δₙ : Sₙ ⊗ᴸ_R K ⟶ K⟦1⟧` for the connecting morphisms of the
natural reduction triangles `K --mⁿ⁺¹--> K --ηₙ--> Sₙ ⊗ᴸ_R K --δₙ--> K⟦1⟧`
(`Mod.derivedExtendScalarsTriangleδ`), so that `tₙ ≫ δₙ = δₙ₊₁ ≫ m`. The maps
`ρₙ = ηₙ(B) ≫ sₙ : B ⟶ Sₙ ⊗ᴸ_R A` are compatible with the transitions, so by
`CategoryTheory.Pretriangulated.exists_comp_eq_of_tower` there is `r : B ⟶ A` with
`r ≫ η₀ = ρ₀` (the Milnor sequence for `A = R lim (Sₙ ⊗ᴸ_R A)`: only the surjectivity onto
`lim Hom(B, Sₙ ⊗ᴸ_R A)` is used, no `lim¹` term needs to vanish). The endomorphism `e = i ≫ r`
satisfies `e ≫ η₀ = η₀`, so `S₀ ⊗ᴸ_R e = 𝟙` and `e` is invertible by derived Nakayama
(`Mod.isIso_of_comp_unit_eq`), and `r ≫ e⁻¹` is a retraction of `i`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C] {R : C} [MonObj R] [IsCommMonObj R]

section Nakayama

variable {S : C} [MonObj S] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ] (k : ℤ)
  (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)

end Nakayama

variable {S : ℕ → C} [∀ n, MonObj (S n)] [∀ n, IsCommMonObj (S n)] {φ : ∀ n, R ⟶ S n}
  [∀ n, IsMonHom (φ n)] {ψ : ∀ n, S (n + 1) ⟶ S n} [∀ n, IsMonHom (ψ n)]
  (hψ : ∀ n, φ (n + 1) ≫ ψ n = φ n) (m : ℤ) (w : ∀ n, ((m ^ (n + 1)) • 𝟙 R) ≫ φ n = 0)
  (hS : ∀ n, (ShortComplex.mk _ _ (w n)).ShortExact)
  [HasCountableProducts (DerivedCategory (Mod C R))]

end CategoryTheory.Mod
