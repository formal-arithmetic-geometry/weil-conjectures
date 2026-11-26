/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Module.ULift
import WeilConjectures.RingTheory.WellOrderedUnionProjectiveDimension
import WeilConjectures.RingTheory.CyclicGlobalDimension
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-!
# Testing global dimension on finite and cyclic modules

Global dimension at most `n` can be tested on finite modules, or on cyclic modules `R ⧸ I`.

## Implementation details

For the nontrivial direction, well-order a generating set of an arbitrary module `M` and
filter `M` by the spans of initial segments. Each successive quotient is cyclic, hence of the
form `R ⧸ I`, and the bound for well-ordered unions of modules of bounded projective dimension
gives the bound for `M`. The lift of `R ⧸ I` only puts the quotient in the universe of the
test modules.

## References

* [Stacks, Tag 065T]
* [Stacks, Tag 00AQ]
-/

@[expose] public section

universe u v

namespace Ring

/-- Global dimension at most `n` can be tested on finite modules or on cyclic quotients. -/
theorem hasGlobalDimensionLE_iff_finite_iff_cyclic (R : Type u) [CommRing R] (n : ℕ) :
    (HasGlobalDimensionLE.{u, max u v} R n ↔
      ∀ M : ModuleCat.{max u v} R, Module.Finite R M →
        ModuleCat.HasProjectiveResolutionLE M n) ∧
    ((∀ M : ModuleCat.{max u v} R, Module.Finite R M →
        ModuleCat.HasProjectiveResolutionLE M n) ↔
      ∀ I : Ideal R,
        ModuleCat.HasProjectiveResolutionLE (ModuleCat.of R (ULift.{v} (R ⧸ I))) n) := by
  let P : Prop := ∀ M : ModuleCat.{max u v} R, Module.Finite R M →
    ModuleCat.HasProjectiveResolutionLE M n
  let C : Prop := ∀ I : Ideal R,
    ModuleCat.HasProjectiveResolutionLE (ModuleCat.of R (ULift.{v} (R ⧸ I))) n
  have hGC : C → HasGlobalDimensionLE.{u, max u v} R n :=
    hasGlobalDimensionLE_of_cyclic R n
  have hGF : HasGlobalDimensionLE.{u, max u v} R n → P := by
    intro h M hM
    exact (hasGlobalDimensionLE_iff R n).1 h M
  have hFC : P → C := by
    intro h I
    apply h
    infer_instance
  have hCF : C → P := fun h => hGF (hGC h)
  exact ⟨⟨hGF, fun h => hGC (hFC h)⟩, ⟨hFC, hCF⟩⟩

end Ring
