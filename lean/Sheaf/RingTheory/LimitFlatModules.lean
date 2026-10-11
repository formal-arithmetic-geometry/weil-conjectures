/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Inverse limits of flat modules over ideal-power quotients

Source: Stacks Project, More on Algebra, Lemma Tag 0912 (lemma-limit-flat).
(blueprint: lem-weil-pbc-limit-flat-modules)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

/-- An inverse system of flat `A / Iⁿ`-modules with surjective transitions has flat limit,
and tensoring with a finite module commutes with this limit.
Source: Stacks Project, More on Algebra, Lemma Tag 0912 (lemma-limit-flat).
(blueprint: lem-weil-pbc-limit-flat-modules)

The object `F.obj (op n)` denotes `M_{n+1}`. The quotient module structures, together
with `IsScalarTower`, say that the given `A`-action factors through `A / I^(n+1)`;
in particular `I^(n+1)` annihilates this object. The tensor comparison is stated as
injectivity into the product and surjectivity onto its compatible sequences. Its
`n`-th component is `1 ⊗ limit.π F (op n)`.

Proof (Tag 0912), following the six steps of the DAG node:
1. For a finite module `Q`, choose a finite free resolution using
   `lem-weil-pbc-finite-free-resolution-noetherian`. By `def-weil-pbc-tor-modules` and
   `lem-weil-pbc-tensor-right-exact`, its tensor complex has homology `Tor₁(Q,N)`
   in degree 1 and `Q ⊗ N` in degree 0, naturally in `N`.
2. By `lem-weil-pbc-tensor-over-quotient-ring` and flatness over the quotient, identify
   `Tor₁(Q,M_n)` with `Tor₁(Q,A/Iⁿ) ⊗[A/Iⁿ] M_n`. Exactness of tensor and
   `lem-weil-pbc-exact-functor-complex-cohomology` give this identification, compatible
   with the transition maps (check on tensor generators).
3. By `lem-weil-pbc-tor-strictly-pro-zero`, sufficiently long transition maps on
   these Tor groups vanish. Thus their systems are Mittag-Leffler, essentially
   constant with value zero, and have zero inverse limit.
4. Apply `lem-weil-pbc-mittag-leffler-complex-limit-homology` to the finite-free
   tensor complexes. Their termwise transitions are surjective. Finite free
   tensor products commute with inverse limits, so degree-zero homology identifies
   `Q ⊗ lim M_n` with `lim (Q ⊗ M_n)`. Tracing generators gives the stated canonical
   comparison, natural in `Q`.
5. By `lem-weil-pbc-flat-fg-ideal-criterion`, flatness reduces to injectivity after
   tensoring injections between finite modules. Use the natural comparison from
   step 4 to reduce this to injectivity of the corresponding inverse-limit map.
6. For an injection `Q → Q'`, put `Q'' = coker(Q → Q')`. Apply
   `lem-weil-pbc-tor-long-exact-first-variable` at every level. The Tor systems for
   `Q'` and `Q''` have zero limits by step 3. Apply
   `lem-weil-pbc-mittag-leffler-complex-limit-homology` again to conclude that the
   limit map on tensors is injective. This proves flatness. -/
theorem limit_flat_of_flat_quotients
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    [∀ n : ℕ, Module (A ⧸ I ^ (n + 1)) (F.obj (op n))]
    [∀ n : ℕ, IsScalarTower A (A ⧸ I ^ (n + 1)) (F.obj (op n))]
    (hflat : ∀ n : ℕ, Module.Flat (A ⧸ I ^ (n + 1)) (F.obj (op n)))
    (hsurj : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom) :
    Module.Flat A (limit F : ModuleCat.{v} A) ∧
      ∀ (Q : Type w) [AddCommGroup Q] [Module A Q] [Module.Finite A Q],
        Function.Injective (LinearMap.pi fun n : ℕ ↦ (limit.π F (op n)).hom.lTensor Q) ∧
          ∀ x : ∀ n : ℕ, TensorProduct A Q (F.obj (op n)),
            (∀ n : ℕ, (F.map (homOfLE (Nat.le_succ n)).op).hom.lTensor Q (x (n + 1))
              = x n) →
            ∃ y : TensorProduct A Q (limit F : ModuleCat.{v} A),
              ∀ n : ℕ, (limit.π F (op n)).hom.lTensor Q y = x n := by
  sorry

end ModuleCat
