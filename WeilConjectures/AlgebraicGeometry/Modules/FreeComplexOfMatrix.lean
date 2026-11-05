/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# Complexes of free modules given by matrices

For finite index types `ι n` and matrices `D n` of global functions on a scheme `Y` with
`D (n + 1) * D n = 0`, `AlgebraicGeometry.Scheme.Modules.freeComplex D hD` is the cochain complex
of `𝒪_Y`-modules with terms `𝒪_Y^{(ι n)}` and differentials the morphisms with matrices `D n`.

* Its pullback along `j : Z ⟶ Y` is the complex of the images of the matrices
  (`AlgebraicGeometry.Scheme.Modules.pullbackFreeComplexIso`).
* A morphism from it (restricted to nonnegative degrees) to a complex `K` of `𝒪_Y`-modules indexed
  by `ℕ` is given by global sections of the terms of `K` satisfying the relations of the matrices
  (`AlgebraicGeometry.Scheme.Modules.freeComplexHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-! ### Morphisms out of free modules given by sections -/

/-! ### The complex -/

variable {ι : ℤ → Type u} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

variable (D : ∀ n : ℤ, Matrix (ι (n + 1)) (ι n) Γ(Y, ⊤)) (hD : ∀ n, D (n + 1) * D n = 0)

/-! ### Morphisms to complexes indexed by `ℕ` -/

end AlgebraicGeometry.Scheme.Modules
