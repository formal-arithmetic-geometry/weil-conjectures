/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.RingTheory.SmoothQuotientFibreFinrankAdd

/-! # Differential rank at points of fibres of a smooth polynomial quotient

## References

* [Stacks, Tag 07CG]
* [Stacks, Tag 07CH]
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

/-- For a smooth quotient `Q` of `R[X₁, …, Xₙ]` by `c` equations whose conormal module is
free on `c` generators, `c ≤ n` and the Kähler differentials of each fibre `κ(p) ⊗[R] Q`
have rank `n - c` at every point. -/
theorem smooth_quotient_fibre_differential_rank
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (p : Ideal R) [p.IsPrime]
    (q : PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    c ≤ n ∧ Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[p.Fiber
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
          KaehlerDifferential p.ResidueField
            (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) = n - c := by
  have h := smooth_quotient_fibre_finrank_add f b p q
  constructor
  · omega
  · omega

end Algebra
