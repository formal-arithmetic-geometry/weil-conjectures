/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology

/-!
# The scalar-defect relation for a central simple algebra

A central simple `K`-algebra `A` has scalar defect `x ∈ H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)` if a splitting
`Kˢᵉᵖ ⊗ A ≅ Mₙ(Kˢᵉᵖ)` admits locally constant matrix lifts of its Galois descent datum whose
failure to be a one-cocycle is a homogeneous two-cocycle representing `x`.

## References

* [Stacks Project, Tags 03R6, 03R7 and 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

variable (K : Type u) [Field K]

/-- A homogeneous degree-two cocycle evaluated in inhomogeneous coordinates, that is, at
`(1, g, g * h)`. -/
noncomputable def galoisUnitsCocycleValue
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2)
    (g h : SeparableClosure K ≃ₐ[K] SeparableClosure K) : (SeparableClosure K)ˣ :=
  ((((TopRep.homogeneousCochains (galoisUnitsTopRep K)).iCycles 2).hom z).val 1 g (g * h)).toMul

/-- `A` realizes the class `x` through matrix lifts of its Galois descent datum.
The splitting is an algebra equivalence after scalar extension, and the matrix lifts
are locally constant for the Krull topology. The last equation specifies their scalar
multiplication defect using a homogeneous cocycle representing `x`. -/
def HasBrauerScalarDefect (A : CSA.{u, u} K) (x : GaloisUnitsH2 K) : Prop :=
  ∃ (n : ℕ) (_ : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)),
    IsLocallyConstant b ∧
    ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z = x ∧
      (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
          b (g * h))

end Field
