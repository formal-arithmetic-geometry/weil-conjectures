/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Flatness of modules descends to a finite stage

Let `R₀` be a noetherian ring, `S₀` a finite type `R₀`-algebra, `M₀` a finite `S₀`-module and
`A` an `R₀`-algebra such that `A ⊗[R₀] M₀` is flat over `A`. Then there is a finitely generated
`R₀`-subalgebra `R₁` of `A` such that `R ⊗[R₀] M₀` is flat over `R` for every subalgebra
`R₁ ≤ R ≤ A` (Stacks, Tags 00R6 and 02JO; EGA IV₃, 11.2.6).

This is the module version of `Module.exists_fg_flat_localization_tensor` and
`PrimeSpectrum.exists_fg_forall_flat_localization_tensor_of_isCompact`, which treat `M₀ = S₀`.

## Main results

- `Module.flat_localizedModule_baseChange_of_forall`: flatness at a prime of a finite stage, by
  the local criterion (Stacks, Tag 00MO).
- `Module.exists_fg_flat_localizedModule_baseChange`: flatness at a prime descends to a finitely
  generated subalgebra (Stacks, Tag 00R6).
- `Module.exists_fg_forall_flat_tensorProduct`: flatness descends to a finitely generated
  subalgebra (Stacks, Tag 02JO).

## Implementation notes

For an `R₀`-algebra `R` we write `B R = R ⊗[R₀] S₀`, an `S₀`-algebra by
`Algebra.TensorProduct.rightAlgebra`, and `N R = B R ⊗[S₀] M₀`, which is a `B R`-module and an
`R`-module; flatness is checked at the localizations of `N R` at primes of `B R`. The key tool is
the identification `N R ⊗[R] K ≃ M₀ ⊗[R₀] K` (`Module.baseChangeTensorEquiv`).
-/

@[expose] public section

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Module

section Equiv

variable {R₀ R₁ S₀ M₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

variable (K : Type*) [AddCommGroup K] [Module R₀ K] [Module R₁ K] [IsScalarTower R₀ R₁ K]

end Equiv

section Localization

variable {R₀ R₁ S₀ M₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

end Localization

section LocalCriterion

universe u

variable {R₀ R₁ S₀ M₀ : Type u} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

end LocalCriterion

section FiniteStage

variable {R₀ A M₀ : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A] [AddCommGroup M₀]
  [Module R₀ M₀]

end FiniteStage

section AtPrime

universe u

variable {R₀ S₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [AddCommGroup M₀]
  [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

end AtPrime

section Global

universe u

variable {R₀ S₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [AddCommGroup M₀]
  [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

end Global

end Module
