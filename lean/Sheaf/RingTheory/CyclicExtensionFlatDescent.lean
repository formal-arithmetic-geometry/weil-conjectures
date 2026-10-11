/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Descent of extensions of cyclic ideal-power quotients

Source: Stacks Project, More on Algebra, Lemma 05EG, the case `M = R/I^n`
(blueprint: lem-weil-pbc-cyclic-extension-flat-descent).

Base change is written `S ⊗[R] M`, as in `LinearMap.baseChange`; tensor symmetry identifies
this with the source's `M ⊗[R] S`. Short exactness is expressed by injectivity, `Function.Exact`,
and surjectivity, the module interpretation of `CategoryTheory.ShortComplex.ShortExact`
via `ShortExact.moduleCat_exact_iff_function_exact` and its injective/surjective lemmas.
-/

universe u v w x

open TensorProduct

namespace LinearMap

/-- An extension of a cyclic ideal-power quotient descends along a flat neighbourhood.
Source: Stacks Project, More on Algebra, Lemma 05EG, second paragraph of the proof
(blueprint: lem-weil-pbc-cyclic-extension-flat-descent).

Proof (the nine steps of the node):
1. Put `J = I^n`. Products of generators of `I` generate `J`; choose generators `f_i`
   (a zero generator is allowed). Form `M_f = R^t/W`, with relations
   `f_i e_j = f_j e_i`, and `μ : M_f → R` sending `e_i` to `f_i`.
   Its image is `J`. If `z = ∑ a_i e_i` belongs to `K = ker μ`, then
   `f_j z = ∑ a_i f_i e_j = 0`, so `J K = 0` (05ED; cyclic-extension-cocycle).
2. For an `R`-module `P`, let `Z_f(P)` consist of tuples with `f_i x_j = f_j x_i`,
   and let `B_f(P)` consist of tuples `(f_i p)`. In `H_1(P) = Z_f(P)/B_f(P)`,
   multiplication of a cycle by `f_i` is the boundary `(f_j x_i)_j`.
   Thus `J H_1(N) = 0` (05EF; cyclic-extension-cocycle and quotient-module).
3. Write `Z_f(N)` as the kernel of `x ↦ (f_i x_j - f_j x_i)` and `B_f(N)` as
   the image of `p ↦ (f_i p)`. Flat tensor exactness, tensor right exactness, and
   tensor finite-product comparison identify `H_1(N) ⊗ S` with `H_1(N ⊗ S)`.
   Torsion-module-flat-base-change-iso (05E9) identifies `H_1(N)` with its tensor
   base change. Every class over `S` therefore comes from a cycle over `R`.
4. Tensor the presentation of `M_f` and the kernel sequence for `μ`.
   Tensor right exactness, flat tensor exactness, and finite-product comparison
   identify their base changes with `M'_f` and `K'` over `S`. The map defined by
   a cycle tensors to the map defined by the tensored cycle. Tensor-quotient-base-change
   gives `κ : C_S ≃ S/JS`, with `r ⊗ s ↦ φ(r)s` modulo `JS`.
5. Lift `1` through `κ b`. The unique `y'_i` with `a(y'_i) = f_i τ` form an
   admissible cycle over `S`. Cyclic-extension-cocycle (2) identifies its extension
   `E_f(N_S,y')` with `T`, preserving the injection and quotient map (05EE).
6. Step 3 gives a cycle `y` over `R` and `m ∈ N_S` with `y_i ⊗ 1 = y'_i + f_i m`.
   Cyclic-extension-cocycle (3), using `-m`, makes `y ⊗ 1` admissible and identifies
   its extension with that of `y'`, preserving both end maps.
7. The restriction of the map defined by `y` to `K` tensors to zero by steps 4 and 6.
   Since `J K = 0`, torsion-hom-flat-comparison (05EC) is injective on these maps.
   The restriction was zero already; hence `y` is admissible over `R`.
8. Cyclic-extension-cocycle (1) gives the exact extension `E = E_f(N,y)`.
   Flat tensor exactness and tensor right exactness give its exact base change.
   The class of `(0,1)` in `E` maps to `1` in `C` and satisfies `f_i e = j(y_i)`.
   Apply cyclic-extension-cocycle (2) to `e ⊗ 1` to identify the extension of
   `y ⊗ 1` with `E_S`, preserving both maps.
9. Compose the isomorphisms in steps 5, 6, and the inverse of step 8.
   This gives `θ : E_S ≃ T`, with `θ j_S = a` and `κ b θ = κ q_S`.
   Cancel `κ` to get `b θ = q_S`. -/
theorem exists_cyclic_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (_hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    {T : Type x} [AddCommGroup T] [Module S T]
    (a : S ⊗[R] N →ₗ[S] T) (b : T →ₗ[S] S ⊗[R] (R ⧸ I ^ n))
    (_ha : Function.Injective a) (_hab : Function.Exact a b)
    (_hb : Function.Surjective b) :
    ∃ (E : Type (max u w)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] (R ⧸ I ^ n)),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] T,
        θ.toLinearMap.comp (j.baseChange S) = a ∧
        b.comp θ.toLinearMap = q.baseChange S := by
  sorry

end LinearMap
