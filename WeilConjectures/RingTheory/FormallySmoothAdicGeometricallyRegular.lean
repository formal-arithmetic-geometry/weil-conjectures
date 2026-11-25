/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularTensorProductOfFormallySmoothAdic

/-!
# Geometric regularity from maximal-ideal-adic formal smoothness

A Noetherian local algebra over a field which is formally smooth for its maximal-ideal-adic
topology is geometrically regular.

## Implementation details

For a finite purely inseparable extension `k₁ / k`, the ring `D = C ⊗[k] k₁` is Noetherian
local and formally smooth over `k₁` for the `m_C D`-adic topology (Tag 07EG), hence for its
maximal-ideal-adic topology. It is therefore regular local (Tag 07EI), so regular, and the
factor swap `C ⊗[k] k₁ ≃ k₁ ⊗[k] C` transports regularity. The main step is
`Algebra.isRegularRing_tensorProduct_of_formallySmoothAdic`.

## References

* [Stacks, Tag 07EL], implication (2) to (1)
* [Stacks, Tag 07EG]
* [Stacks, Tag 07EI]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A Noetherian local algebra over a field which is formally smooth for its maximal-ideal-adic
 topology is geometrically regular. -/
theorem isGeometricallyRegular_of_formallySmoothAdic (k : Type u) (C : Type v)
    [Field k] [CommRing C] [Algebra k C] [IsNoetherianRing C] [IsLocalRing C]
    (h : FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)) :
    IsGeometricallyRegular k C := by
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  exact isRegularRing_tensorProduct_of_formallySmoothAdic k C k' h

end Algebra
