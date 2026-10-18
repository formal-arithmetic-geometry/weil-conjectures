/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
import Sheaf.TraceFormula.RationalConeDualFinite

/-!
# Integral dual forms for pointed rational cones

Source: `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`,
Expose VIII, Remark 3.1.29, printed p. 103; the integral lattice formulation is
expanded from the rational polyhedral cone description (Kato 1994, *Toric singularities*).
(blueprint: lem-trf-rational-cone-dual-integral-forms)
-/

@[expose] public section

universe u

open scoped TensorProduct

/--
(blueprint: lem-trf-rational-cone-dual-integral-forms)
Source: `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`,
Expose VIII, Remark 3.1.29, printed p. 103 (Kato 1994, *Toric singularities*, WANTED).

Let `L` be a finite free abelian group, `V = ℚ ⊗[ℤ] L` (canonically `L ⊗[ℤ] ℚ`), and
let `C ⊆ V` be the cone of nonnegative rational combinations of `v₁, …, vₘ ∈ L`
(`m = 0` allowed).  If `C` is pointed and every vector of `V` is a difference of two
elements of `C`, then there are `r ≥ 0` and homomorphisms `φᵢ : L → ℤ` whose rational
extensions `Φᵢ` span `Hom_ℚ(V, ℚ)` and cut out `C` by `Φᵢ ≥ 0`.  When `V = 0` the family
is empty; when `V ≠ 0` every such family has `r ≥ 1`.

Proof (from the DAG node).
1. By `lem-trf-rational-cone-dual-finite`, applied to `V` and the `vⱼ`, there are finitely
   many rational forms `λᵢ : V → ℚ` with `C = {x | λᵢ x ≥ 0 for all i}`.  If `V = 0`, take
   the empty family; assume `V ≠ 0`.
2. Write each `λᵢ` in the dual of a `ℤ`-basis of `L` and multiply it by a positive integer
   `dᵢ` clearing denominators; `φᵢ = dᵢ λᵢ` maps `L` into `ℤ`, and the nonnegative locus
   and the `ℚ`-span are unchanged.
3. If `x` is killed by every `φᵢ`, then `x` and `-x` lie in `C`, so `x = 0` by pointedness;
   a family with zero common kernel spans the dual in finite dimension.  As `V ≠ 0`, its
   dual is nonzero, so a spanning family is nonempty: `r ≥ 1`.
-/
theorem rationalConeDualIntegralForms
    (L : Type u) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (m : ℕ) (v : Fin m → L) :
    let V := ℚ ⊗[ℤ] L
    let C : Set V := {x | ∃ q : Fin m → ℚ≥0,
      x = ∑ j, (q j : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) (v j)}
    (C ∩ (-C) = ({0} : Set V)) →
      (∀ x : V, ∃ c₁ ∈ C, ∃ c₂ ∈ C, x = c₁ - c₂) →
      (∃ (r : ℕ) (φ : Fin r → L →+ ℤ) (Φ : Fin r → V →ₗ[ℚ] ℚ),
        (∀ (i : Fin r) (ℓ : L),
          Φ i (TensorProduct.tmul ℤ (1 : ℚ) ℓ) = (φ i ℓ : ℚ)) ∧
        Submodule.span ℚ (Set.range Φ) = ⊤ ∧
        C = {x | ∀ i, 0 ≤ Φ i x} ∧
        ((∀ x : V, x = 0) → r = 0)) ∧
      ((∃ x : V, x ≠ 0) →
        ∀ (r : ℕ) (φ : Fin r → L →+ ℤ) (Φ : Fin r → V →ₗ[ℚ] ℚ),
          (∀ (i : Fin r) (ℓ : L),
            Φ i (TensorProduct.tmul ℤ (1 : ℚ) ℓ) = (φ i ℓ : ℚ)) →
          Submodule.span ℚ (Set.range Φ) = ⊤ →
          C = {x | ∀ i, 0 ≤ Φ i x} → 0 < r) := by
  sorry

end
