module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section
universe u
namespace Field
open scoped TensorProduct
/-- The descent construction produces a bijective algebra homomorphism over the base.
The proof is the matrix Hilbert 90 and finite Galois descent argument from Stacks Tag 03R7.
(blueprint: lem-sc-galois-matrix-cocycle-descent) -/
theorem exists_algHom_matrix_of_galois_cocycle (K : Type u) [Field K]
    (D : Type u) [Ring D] [Algebra K D] (n : ℕ)
    (e : (SeparableClosure K ⊗[K] D) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : Gal(SeparableClosure K/K)) (a : D),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    ∃ f : D →ₐ[K] Matrix (Fin n) (Fin n) K, Function.Bijective f := by
  sorry
end Field
