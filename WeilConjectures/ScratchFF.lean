module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.TensorProduct.Quotient

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem Ideal.map_span_singleton_pow_eq_span_singleton_pow_mul {ϖE : R} {ϖL : S} {e : ℕ}
    {v : S} (hv : IsUnit v) (h : algebraMap R S ϖE = v * ϖL ^ e) (n : ℕ) :
    (Ideal.span {ϖE ^ n}).map (algebraMap R S) = Ideal.span {ϖL ^ (e * n)} := by
  rw [Ideal.map_span, Set.image_singleton, map_pow, h, mul_pow, pow_mul,
    Ideal.span_singleton_mul_left_unit (hv.pow n)]

theorem Module.free_quotient_map_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R S] [Module.IsTorsionFree R S] (I : Ideal R) :
    Module.Free (R ⧸ I) (S ⧸ I.map (algebraMap R S)) ∧
      Module.Finite (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  have : Module.Free R S := Module.free_of_finite_type_torsion_free'
  let e := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  have := Module.Finite.base_change R (R ⧸ I) S
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
