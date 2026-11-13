/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ValuationClosedFibreIntegral
import WeilConjectures.AlgebraicGeometry.ValuationClosedFibreSectionDivisible

/-! # Vanishing on the closed fibre implies divisibility

## References

* [Stacks Project, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- A section vanishing on the closed fibre is divisible by an element of the maximal ideal. -/
theorem closed_fibre_vanishing_is_divisible
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hX₀ : IsIntegral (Limits.pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))
    (s : Γ(L, ⊤)) :
    IsIntegral (f.fiber (IsLocalRing.closedPoint A)) ∧
      (((Classical.choose (exists_tensorPullbackAdjunction
        (f.fiberι (IsLocalRing.closedPoint A)))).unit.app L).val.app (op ⊤) s = 0 →
        ∃ π : A, π ∈ IsLocalRing.maximalIdeal A ∧ ∃ t : Γ(L, ⊤),
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π • t = s) := by
  refine ⟨closed_fibre_is_integral A X f hX₀, ?_⟩
  exact closed_fibre_section_is_divisible A X f L hX₀ s

end AlgebraicGeometry.Scheme.Modules
