/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Isolated fibre points and quasi-finiteness on affine pairs

## References

* Stacks Project, Morphisms, Tag 01TH, (2) implies (4), and Tag 01T2.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An isolated point of the fibre of a locally finite type morphism gives a finite-type
ring map, quasi-finite at the corresponding prime, on every affine pair containing the
point. (Stacks, Tags 01TH, 01T2)

The algebra structure is the one induced by the map on sections. -/
theorem Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hisolated : IsOpen ({f.asFiber x} : Set (f.fiber (f x))))
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hx : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := (f.appLE V U hUV).hom.toAlgebra
    ∃ hft : Algebra.FiniteType Γ(S, V) Γ(X, U),
      letI := hft
      Algebra.IsQuasiFiniteAtPrime Γ(S, V) Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩) := by
  let := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra.FiniteType Γ(S, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  refine ⟨inferInstance, ?_⟩
  have hq := (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr hisolated).quasiFiniteAt
    hU hV hUV hx
  have hopen := (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber
    (R := Γ(S, V)) (hU.primeIdealOf ⟨x, hx⟩)).mp hq
  let q := hU.primeIdealOf ⟨x, hx⟩
  let e := PrimeSpectrum.preimageHomeomorphFiber Γ(S, V) Γ(X, U)
    (q.comap (algebraMap Γ(S, V) Γ(X, U)))
  change IsOpen {e ⟨q, rfl⟩}
  rw [← Set.image_singleton, e.isOpen_image]
  exact hopen

end AlgebraicGeometry
