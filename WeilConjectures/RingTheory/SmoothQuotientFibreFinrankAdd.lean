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

import WeilConjectures.RingTheory.SmoothQuotientFibreFinrankAddLe
import WeilConjectures.RingTheory.SmoothQuotientFibreFinrankEqSub

/-!
# Rank additivity for fibres of a smooth polynomial quotient

For a smooth polynomial quotient in `n` variables whose conormal module is free of rank `c`, we
show that the fibre of the Kähler differentials at any point over a prime of the base has
dimension `n - c`, in the additive form `c + d = n`.

## References

* [Stacks, Tag 07CG]
* [Stacks, Tag 07CH]
-/

@[expose] public section


universe u

open scoped TensorProduct

namespace Algebra

/-- For a smooth polynomial quotient `C = R[x₁, ..., xₙ]/(f₁, ..., f_c)` whose conormal module is
free with basis indexed by `Fin c`, and a point `q` of the fibre of `C` over a prime `p` of `R`,
`c` plus the dimension over `κ(q)` of the fibre of the Kähler differentials of `C ⊗ κ(p)` over
`κ(p)` equals `n`. -/
theorem smooth_quotient_fibre_finrank_add
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (p : Ideal R) [p.IsPrime]
    (q : PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    c + Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[p.Fiber
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
          KaehlerDifferential p.ResidueField
            (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) = n := by
  have hsub : c ≤ n := by
    exact smooth_quotient_fibre_finrank_add_le f b p q
  have hdim : Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[p.Fiber
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
          KaehlerDifferential p.ResidueField
            (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) = n - c := by
    exact smooth_quotient_fibre_finrank_eq_sub f b p q
  omega


end Algebra
