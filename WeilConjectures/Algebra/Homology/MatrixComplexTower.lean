/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.MatrixComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-!
# Towers of matrix complexes over an adic ring

Let `R` be a commutative ring with a tower of quotients `π n : R →+* A n` and transitions
`ρ n : A (n + 1) →+* A n` with `π n = ρ n ∘ π (n + 1)`, and assume that `R` is complete and
separated for the tower: every compatible family `(xₙ)` comes from a unique `x ∈ R`.

A family of matrix complexes `M n` over `A n` with fixed ranks whose matrices are compatible
under the transitions defines a tower `n ↦ Res (M n)` of complexes of `R`-modules
(`MatrixComplex.towerFunctor`). A matrix complex `M` over `R` reducing to the `M n` gives a cone
over this tower (`MatrixComplex.towerCone`), which is a limit cone
(`MatrixComplex.isLimitTowerCone`). Its image in the derived category is therefore a homotopy
limit cone (`MatrixComplex.isHomotopyLimit_towerCone`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace MatrixComplex

variable {R : Type u} [CommRing R] {A : ℕ → Type u} [∀ n, CommRing (A n)]
  {π : ∀ n, R →+* A n} {ρ : ∀ n, A (n + 1) →+* A n}

section Elements

variable (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)

end Elements

variable (hρ : ∀ n, π n = (ρ n).comp (π (n + 1))) {r : ℤ → ℕ} (M : ∀ n, MatrixComplex r (A n))
  (hM : ∀ n i, ((M (n + 1)).d i).map (ρ n) = (M n).d i)

section Lim

variable (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)
  (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)

end Lim

variable {M} (M' : MatrixComplex r R) (hM' : ∀ n i, (M'.d i).map (π n) = (M n).d i)

variable (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)
  (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)

section Limit

variable {i : ℤ} (s : Cone (towerFunctor hρ M hM ⋙ HomologicalComplex.eval _ _ i))

end Limit

end MatrixComplex
