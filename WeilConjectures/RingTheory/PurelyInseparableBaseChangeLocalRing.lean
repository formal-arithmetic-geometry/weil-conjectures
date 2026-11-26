/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.Dimension.Finite
import WeilConjectures.RingTheory.PurelyInseparableBaseChangeStructural
import WeilConjectures.RingTheory.PurelyInseparableBaseChangeResidue

/-! # Purely inseparable base change of a Noetherian local algebra

For a Noetherian local `k`-algebra `A` and a finite purely inseparable extension `k'/k`, the base
change `A' = A ⊗_k k'` is finite free, flat, Noetherian and local, with closed fibre of dimension
`[k' : k]` and finite residue field extension.

## Implementation details

A `k`-basis of `k'` gives an `A`-basis of `A'`. The closed fibre is `K ⊗_k k'`, in which every
element is a unit or nilpotent (some `p`-power lies in `K`), so its nilradical is the unique
prime. Its inverse image `m'` is the only prime containing `mA'`, and every maximal ideal of the
finite algebra `A'` contains `mA'`, so `A'` is local with residue field a quotient of the closed
fibre.

## References

* [Stacks, Tag 07E5] (proof of (3) ⇒ (1))
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Base change of a Noetherian local algebra along a finite purely inseparable extension is
finite free, flat, Noetherian and local, with the stated closed fibre and finite residue extension.
-/
theorem purelyInseparable_baseChange_localRing
    (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A]
    [IsPurelyInseparable k k'] [Module.Finite k k']
    [IsLocalRing A] [IsNoetherianRing A] :
    Nonempty (Module.Basis (Fin (Module.finrank k k')) A (A ⊗[k] k')) ∧
      Module.Free A (A ⊗[k] k') ∧
      Module.Finite A (A ⊗[k] k') ∧
      RingHom.Flat (algebraMap A (A ⊗[k] k')) ∧
      IsNoetherianRing (A ⊗[k] k') ∧
      IsLocalRing (A ⊗[k] k') ∧
      (∃ m' : Ideal (A ⊗[k] k'),
        m'.IsMaximal ∧
        (∀ P : Ideal (A ⊗[k] k'), P.IsPrime →
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A) ≤ P ↔
            P = m')) ∧
        (∃ f : IsLocalRing.ResidueField A →+* ((A ⊗[k] k') ⧸ m'),
          (∀ a : A, f (IsLocalRing.residue A a) =
            Ideal.Quotient.mk m' (algebraMap A (A ⊗[k] k') a)) ∧
          @Module.Finite (IsLocalRing.ResidueField A) ((A ⊗[k] k') ⧸ m')
            _ _ (@Algebra.toModule _ _ _ _ f.toAlgebra))) ∧
      (∃ e : ((A ⊗[k] k') ⧸
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))) ≃+*
          ((IsLocalRing.ResidueField A) ⊗[k] k'),
        (∀ (a : A) (x : k'),
          e (Ideal.Quotient.mk
            (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))
            (a ⊗ₜ[k] x)) = (IsLocalRing.residue A a) ⊗ₜ[k] x) ∧
        @Module.finrank (IsLocalRing.ResidueField A)
          ((A ⊗[k] k') ⧸
            (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A)))
          _ _ (@Algebra.toModule _ _ _ _
            (e.symm.toRingHom.comp
              (algebraMap (IsLocalRing.ResidueField A)
                ((IsLocalRing.ResidueField A) ⊗[k] k'))).toAlgebra) =
            Module.finrank k k') := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ :=
    purelyInseparable_baseChange_structural k k' A
  obtain ⟨h₆, h₇, h₈⟩ :=
    purelyInseparable_baseChange_residue k k' A
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

end Algebra.TensorProduct
