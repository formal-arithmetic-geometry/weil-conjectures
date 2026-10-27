/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Sheaf.RingTheory.LocalEssentiallyFinitePresentationModInjective
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Universal injectivity of localization at closed-fibre regular scalars

Source: Stacks Project, More on Flatness, Tag 05DF,
`lemma-homothety-universally-injective` in `flat.tex`
(blueprint: lem-sfb-fibre-regular-localization-universal-injection).
-/

@[expose] public section

set_option autoImplicit false

universe u v p w t

open scoped TensorProduct

namespace Algebra

/-- Scalars regular on the closed fibre form a multiplicative set. Each acts universally
injectively over the base, and localization at this set is universally injective too.
The quotient by the extended maximal ideal is `N / m_R N`, as an `S`-module.
`nonZeroSMulDivisors` is exactly the set of scalars acting injectively on this quotient,
by `isSMulRegular_iff_mem_nonZeroSMulDivisors`. The first two clauses explicitly state
that it contains one and is closed under multiplication.

Source: Stacks Project, More on Flatness, Tag 05DF,
`lemma-homothety-universally-injective`
(blueprint: lem-sfb-fibre-regular-localization-universal-injection).

Proof:
1. Multiplication by one is the identity. If multiplication by `s` and by `t` is
   injective on the closed fibre, their composite is multiplication by `s * t` and
   is injective. This supplies the multiplicative subset used in localization.
2. For a closed-fibre regular `s`, apply
   lem-trf-valuation-general-mod-injective to the `S`-linear multiplication map
   on `N`. The presentation by `B` and `W` supplies essential finite presentation;
   the source and target are finitely presented, the target is `R`-flat, and the
   reduction is injective. The map is injective and `N / sN` is `R`-flat.
3. Apply lem-weil-pbc-flat-quotient-tensor-injective to this short exact sequence
   and an arbitrary `R`-module `L`. Tensor symmetry identifies its injective map
   on `L ⊗[R] N` with multiplication by `s` on `N ⊗[R] L`, on pure tensors and
   hence everywhere by the tensor universal property
   (def-weil-pbc-module-tensor-product).
4. By lem-weil-pbc-localization-tensor-over-base, tensoring the localization map
   with `L` is the localization of `N ⊗[R] L` at this same multiplicative subset.
   Its formula is `(n ⊗ l) / s ↦ (n / s) ⊗ l`.
5. If an element maps to zero, the fraction-zero criterion of
   def-weil-pbc-module-localization gives a closed-fibre regular `s` annihilating
   it. Step 3 makes multiplication by this `s` injective, so the element is zero.
   Thus the tensor of the localization map is injective for every `L`.
-/
theorem fibre_regular_localization_universally_injective
    {R : Type u} {S : Type v} {B : Type p} {N : Type w}
    [CommRing R] [CommRing S] [CommRing B] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R B] [Algebra B S] [IsScalarTower R B S]
    [Algebra.FinitePresentation R B] (W : Submonoid B) [IsLocalization W S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N] :
    IsSMulRegular
      (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
        (⊤ : Submodule S N))) (1 : S) ∧
    (∀ s t : S,
      IsSMulRegular
        (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S N))) s →
      IsSMulRegular
        (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S N))) t →
      IsSMulRegular
        (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S N))) (s * t)) ∧
    (∀ s : S,
      IsSMulRegular
        (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
          (⊤ : Submodule S N))) s →
      ∀ (L : Type (max u v p w t)) [AddCommGroup L] [Module R L],
        IsSMulRegular (N ⊗[R] L) s) ∧
    (∀ (L : Type (max u v p w t)) [AddCommGroup L] [Module R L],
      Function.Injective
        (((LocalizedModule.mkLinearMap
          (nonZeroSMulDivisors S
            (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
              (⊤ : Submodule S N)))) N).restrictScalars R).rTensor L)) := by
  sorry

end Algebra
