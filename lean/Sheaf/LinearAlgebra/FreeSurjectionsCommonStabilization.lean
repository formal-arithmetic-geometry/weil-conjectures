/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.StdBasis

/-!
# Common zero stabilization of finite free generating surjections

Source: Stacks Project, More on Algebra, Tag 07Z8 (`lemma-fitting-ideal`),
final proof paragraph; Algebra, Tag 00O3 (`lemma-Schanuel`), commuting diagram
(blueprint: lem-trf-free-surjections-common-stabilization).

The finite free modules are represented by `Fin n → R` and `Fin m → R`.
Binary direct sums are represented by products. The equivalence is characterized
by its forward and inverse formulas for every pair of lifts.
-/

@[expose] public section

universe u v

namespace Module

/-- Two finite free generating surjections have a common zero stabilization.

Source: Stacks Project, More on Algebra, Tag 07Z8 (`lemma-fitting-ideal`),
final proof paragraph, with the explicit shears from Algebra, Tag 00O3
(`lemma-Schanuel`)
(blueprint: lem-trf-free-surjections-common-stabilization).

Proof:
1. The standard bases make `Fin n → R` and `Fin m → R` free
   (def-weil-pbc-free-module). They are projective by
   lem-weil-pbc-free-module-projective (`Module.Projective.of_free`). Apply
   def-weil-pbc-projective-module's lifting property
   (`Module.projective_lifting_property`) to `π` and `π'` to obtain `f`, and
   to `π'` and `π` to obtain `g`, with the two required composition equations.
2. For any such lifts, the displayed maps `U` and `V` are linear: their
   coordinates are sums and differences of composites of linear maps and
   projections. For `b = x - f y` and `a = y + g b`, one has `a - g b = y`
   and `b + f (a - g b) = x`, so `V (U (x,y)) = (x,y)`. Conversely, put
   `y = a - g b` and `x = b + f y`; then `x - f y = b` and
   `y + g (x - f y) = a`, proving `U (V (a,b)) = (a,b)`.
3. The lift equations give
   `π' (y + g (x - f y)) = π' y + π x - π (f y) = π x`.
   Thus the zero-stabilized quotient maps commute with `U`.
4. The kernels of those quotient maps are `(ker π).prod ⊤` and
   `(ker π').prod ⊤`. The commuting equation gives the forward inclusion
   of their images under `U`. For the reverse inclusion, take a vector `w`
   in the latter kernel and use `z = U.symm w`; then `p z = q w = 0`
   and `U z = w`.
-/
theorem free_surjections_common_stabilization
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n m : ℕ) (π : (Fin n → R) →ₗ[R] M) (π' : (Fin m → R) →ₗ[R] M)
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π') :
    (∃ (f : (Fin m → R) →ₗ[R] (Fin n → R))
        (g : (Fin n → R) →ₗ[R] (Fin m → R)),
      π.comp f = π' ∧ π'.comp g = π) ∧
    (∀ (f : (Fin m → R) →ₗ[R] (Fin n → R))
        (g : (Fin n → R) →ₗ[R] (Fin m → R)),
      π.comp f = π' → π'.comp g = π →
      ∃ U : ((Fin n → R) × (Fin m → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)),
        (∀ (x : Fin n → R) (y : Fin m → R),
          U (x, y) = (y + g (x - f y), x - f y)) ∧
        (∀ (a : Fin m → R) (b : Fin n → R),
          U.symm (a, b) = (b + f (a - g b), a - g b)) ∧
        (π'.comp (LinearMap.fst R (Fin m → R) (Fin n → R))).comp U.toLinearMap =
          π.comp (LinearMap.fst R (Fin n → R) (Fin m → R)) ∧
        Submodule.map U.toLinearMap ((LinearMap.ker π).prod ⊤) =
          (LinearMap.ker π').prod ⊤) := by
  constructor
  · obtain ⟨f, hf⟩ := projective_lifting_property π π' hπ
    obtain ⟨g, hg⟩ := projective_lifting_property π' π hπ'
    exact ⟨f, g, hf, hg⟩
  · intro f g hf hg
    let d := LinearMap.fst R (Fin n → R) (Fin m → R) -
      f.comp (LinearMap.snd R (Fin n → R) (Fin m → R))
    let U : ((Fin n → R) × (Fin m → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)) :=
      { (LinearMap.snd R (Fin n → R) (Fin m → R) + g.comp d).prod d with
        invFun := fun z ↦ (z.2 + f (z.1 - g z.2), z.1 - g z.2)
        left_inv := by
          rintro ⟨x, y⟩
          simp [d]
        right_inv := by
          rintro ⟨a, b⟩
          simp [d] }
    have hf_apply (y : Fin m → R) : π (f y) = π' y := DFunLike.congr_fun hf y
    have hg_apply (x : Fin n → R) : π' (g x) = π x := DFunLike.congr_fun hg x
    have hcomm (z : (Fin n → R) × (Fin m → R)) : π' (U z).1 = π z.1 := by
      simp [U, d, hf_apply, hg_apply]
    refine ⟨U, ?_, ?_, ?_, ?_⟩
    · intro x y
      rfl
    · intro a b
      rfl
    · apply LinearMap.ext
      intro z
      exact hcomm z
    · apply le_antisymm
      · rintro w ⟨z, hz, rfl⟩
        have hz' : π z.1 = 0 := hz.1
        change π' (U z).1 = 0 ∧ (U z).2 ∈ (⊤ : Submodule R (Fin n → R))
        exact ⟨(hcomm z).trans hz', Submodule.mem_top⟩
      · intro w hw
        refine ⟨U.symm w, ?_, U.apply_symm_apply w⟩
        have hw' : π' w.1 = 0 := hw.1
        change π (U.symm w).1 = 0 ∧ (U.symm w).2 ∈ (⊤ : Submodule R (Fin m → R))
        exact ⟨(hcomm (U.symm w)).symm.trans (by simpa using hw'), Submodule.mem_top⟩

end Module
