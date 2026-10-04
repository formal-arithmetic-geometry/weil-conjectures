/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections of quasi-coherent modules over basic opens of an affine open

Let `M` be a quasi-coherent `𝒪_X`-module, `W` an affine open subscheme of `X` and `f ∈ Γ(X, W)`.
Then the restriction `Γ(M, W) → Γ(M, D(f))` is a localization at the powers of `f`. We record the
two halves of this statement elementwise: every section over `D(f)` becomes, after multiplication
by a power of `f`, the restriction of a section over `W`; and a section over `W` vanishing on `D(f)`
is killed by a power of `f`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen`
- `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen`
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]

/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. Every section of `M` over
`D(f)` becomes the restriction of a section over `W` after multiplication by a power of `f`. -/
lemma exists_map_eq_pow_smul_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, W)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s :=
  sorry

/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. A section of `M` over `W`
whose restriction to `D(f)` vanishes is killed by a power of `f`. -/
lemma exists_pow_smul_eq_zero_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W))
    (t : Γ(M, W)) (ht : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Modules
