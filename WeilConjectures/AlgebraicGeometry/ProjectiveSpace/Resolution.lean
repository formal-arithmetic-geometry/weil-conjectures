/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Koszul
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.Modules.FlatResolution
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-!
# Resolutions by twists on the projective line

Let `k` be a field. Every coherent module `𝒢` on `ℙ¹_k` has a resolution
`0 → ⨁ 𝒪(-N - 1) → ⨁ 𝒪(-N) → 𝒢 → 0` by finite direct sums of twists.

This replaces the graded Hilbert syzygy theorem of the blueprint by the Castelnuovo–Mumford
regularity argument on `ℙ¹`. Call `ℱ` *`0`-regular* if `H¹(ℱ(-1)) = 0`.

- If `ℱ` is `0`-regular, then a morphism `φ : ℰ ⟶ ℱ` which is surjective on `H⁰` is an
  epimorphism: tensoring the Koszul sequences `0 → 𝒪(a) → 𝒪(a + 1)² → 𝒪(a + 2) → 0` with `ℱ`
  shows that `H⁰(ℱ(m))² ⟶ H⁰(ℱ(m + 1))` is surjective for `m ≥ 0`, so `H⁰(φ(m))` is surjective
  for all `m ≥ 0`; by Serre vanishing the cokernel of `φ` then has no sections after any large
  twist, hence vanishes.
- If moreover `H⁰(ℱ(-1)) = 0`, then the evaluation `H⁰(ℱ) ⊗ 𝒪 ⟶ ℱ` is an isomorphism.
- For coherent `𝒢`, choose `N` with `𝒢(N)` `0`-regular (Serre vanishing). The kernel `𝒦` of the
  evaluation `H⁰(𝒢(N)) ⊗ 𝒪 ⟶ 𝒢(N)` satisfies `H⁰(𝒦) = H¹(𝒦) = 0`, so `𝒦(1)` is trivial.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.exists_shortExact_sigma_twist`: the resolution of length one.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules

variable {k : Type u} [Field k]

local notation3 "𝒪(" a ")" => ProjectiveSpace.twist (ULift (Fin 2)) (Spec (CommRingCat.of k)) a

section RightExact

variable {S : ShortComplex (ProjectiveLine (Spec (.of k))).Modules} (hS : S.Exact)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

end RightExact

section Generalities

variable {X : Scheme.{u}}

end Generalities

section Koszul

variable (M : (ProjectiveLine (Spec (.of k))).Modules) (a : ℤ)

end Koszul

section Regularity

variable (M : (ProjectiveLine (Spec (.of k))).Modules)

end Regularity

section Twisting

end Twisting

section Epi

end Epi

section Finiteness

end Finiteness

section Evaluation

end Evaluation

section Resolution

end Resolution

end AlgebraicGeometry.ProjectiveLine
