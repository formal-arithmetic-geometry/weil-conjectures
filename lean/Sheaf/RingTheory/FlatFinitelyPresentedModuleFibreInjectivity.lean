/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Sheaf.RingTheory.WeakAssLocalization
import Sheaf.RingTheory.LocalUniversalInjectiveResidue

/-! # Fibrewise injectivity for a flat finitely presented localization module

Source: Stacks Project, More on Flatness, Tag 0AT9, lemma-universally-injective-if-flat,
in the situation equation-star
(blueprint: lem-sfb-flat-finitely-presented-module-fibre-injectivity).
-/

@[expose] public section

universe u v w x y

namespace Module

/-- Let `B` be a finitely presented `A`-algebra and `S` a multiplicative subset of `B`.
If `N` is finitely presented over `Localization S` and flat over `A`, and `M` is any
flat `A`-module, an `A`-linear map `f : N →ₗ[A] M` injective on every residue-field
fibre remains injective after tensoring with every `A`-module. The scalar tower
identifies the given `A`-action on `N` with restriction from `Localization S`.

Source: Stacks Project, More on Flatness, Tag 0AT9, lemma-universally-injective-if-flat,
with equation-star
(blueprint: lem-sfb-flat-finitely-presented-module-fibre-injectivity).

Proof:
1. By lem-sfb-flat-target-ideal-quotient-injectivity-test it suffices to prove
   injectivity modulo each finitely generated ideal `J` of `A`. Base change to `A/J`:
   finite algebra and module presentations descend by reducing coefficients, and
   localization commutes with this base change by the fraction maps
   `(b/s) ⊗ ā ↦ ā b̄/s̄` and `b̄/s̄ ↦ (b/s) ⊗ 1`. Flatness persists by
   lem-weil-pbc-flat-module-base-change; primes above `J` have the same residue fields.
   Thus it suffices to prove ordinary injectivity for arbitrary data as stated.
2. If `0 ≠ x ∈ ker f`, choose a prime minimal over its proper annihilator by
   lem-weil-pbc-minimal-prime-over-proper-ideal. By lem-sc-weakass-localization,
   localizing the cyclic module `Ax` gives a nonzero kernel element `z` whose
   annihilator has radical the maximal ideal. Localization embeds this cyclic module
   in the localized `N`, since a fraction vanishes exactly when a denominator kills
   its numerator. Base change preserves all hypotheses as in step 1.
3. Apply lem-sfb-local-finite-presentation-pure-spreadout over this local ring:
   there are a finitely generated ideal `I` inside the maximal ideal, an `A/I`-projective
   module `P`, and a universally injective localization map `j : P → N/IN`.
   The target `M/IM` is flat over `A/I`. For each `s ∈ S`, the map
   `vₛ = f̄ ∘ (1/s) ∘ j` is injective on the closed fibre: `j` is universally injective,
   multiplication by `1/s` is invertible, and `f̄` has the assumed fibre injection.
   By lem-trf-local-universal-injective-residue every `vₛ` is universally injective.
4. Each element of `(N/IN) ⊗ T` comes from `P ⊗ T` under `(1/s)j ⊗ 1` for one
   denominator `s`: write a finite sum of pure tensors and multiply the denominators.
   If its image under `f̄ ⊗ 1` vanishes, step 3 kills the lift. Thus `f̄` is universally
   injective, equivalently `f ⊗ 1_T` is injective for every module killed by `I`.
5. Choose generators `aᵢ` of `I` and positive exponents `eᵢ` with `aᵢ^eᵢ z = 0`.
   Taking `n = 1 + ∑ (eᵢ - 1)` gives `I^n z = 0` by the monomial pigeonhole
   argument, also with `n = 1` if the generator list is empty. Put `K = Ann_A(I^n)`.
   The filtration `K ⊇ IK ⊇ ⋯ ⊇ I^n K = 0` has quotients killed by `I`.
   By lem-weil-pbc-flat-tensor-exact and step 4, descending induction through its
   short exact sequences makes `f ⊗ 1_K` injective.
6. List the finitely many monomial generators `bᵢ` of `I^n`. Tensor the exact sequence
   `0 → K → A → A^t`, with last arrow `a ↦ (bᵢ a)`, with the flat module `N`.
   By lem-weil-pbc-flat-tensor-exact, `N ⊗ K` identifies with `Ann_N(I^n)`, so `z`
   lifts to a nonzero tensor. Tensoring `K ↪ A` with the flat module `M` is injective.
   Naturality, sending `n ⊗ k` to `k • f(n)`, shows that this lift lies in the kernel
   of `f ⊗ 1_K`, contrary to step 5. This proves ordinary injectivity, and step 1
   gives universal injectivity.
-/
theorem flat_finitePresentation_universallyInjective_of_fibres
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B] (S : Submonoid B)
    {N : Type w} [AddCommGroup N] [Module (Localization S) N] [Module A N]
    [IsScalarTower A (Localization S) N]
    [Module.FinitePresentation (Localization S) N] [Module.Flat A N]
    {M : Type x} [AddCommGroup M] [Module A M] [Module.Flat A M]
    (f : N →ₗ[A] M)
    (hfib : ∀ (p : Ideal A) [p.IsPrime], Function.Injective (f.rTensor p.ResidueField)) :
    ∀ (Q : Type (max u v w x y)) [AddCommGroup Q] [Module A Q],
      Function.Injective (f.rTensor Q) := by
  sorry

end Module
