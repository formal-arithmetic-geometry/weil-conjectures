/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.TorDimensionShiftNatural

/-!
# Dimension shifting for Tor along a free presentation

## References

* Stacks Project, Algebra, proof of Tag 00S2, and Tags 00LY and 00LZ
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- Dimension shifting for Tor along `0 → K → F → M → 0`, with `F` free.
The objects `S.X₁`, `S.X₂`, `S.X₃` represent `K`, `F`, `M`, respectively,
and `S.f`, `S.g` represent the maps `j`, `p`. Tor is derived in its first variable. -/
theorem tor_dimension_shift_free
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂] (N : ModuleCat.{u} R) :
    (∀ (i : ℕ), 1 ≤ i →
      Nonempty ((((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).obj N) ≅
        (((Tor' (ModuleCat.{u} R) i).obj S.X₁).obj N))) ∧
    (Limits.IsZero (((Tor' (ModuleCat.{u} R) 2).obj S.X₃).obj N) ↔
      Limits.IsZero (((Tor' (ModuleCat.{u} R) 1).obj S.X₁).obj N)) := by
  have hshift : ∀ i : ℕ, 1 ≤ i →
      Nonempty ((((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).obj N) ≅
        (((Tor' (ModuleCat.{u} R) i).obj S.X₁).obj N)) := by
    intro i hi
    obtain ⟨θ, _⟩ := tor_dimension_shift_natural S hS i hi
    exact ⟨θ N⟩
  refine ⟨hshift, ?_⟩
  obtain ⟨e⟩ := hshift 1 (by decide)
  exact ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

end CategoryTheory
