module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

universe u
open scoped TensorProduct
namespace Algebra

/--
Source: Stacks Project, Smoothing Ring Maps, Lemmas 07CG and 07CH.
(blueprint: new-smooth-quotient-fibre-finrank-add-le)
The split conormal sequence embeds a rank-c summand in the rank-n polynomial
differential module, hence c ≤ n.
-/
theorem smooth_quotient_fibre_finrank_add_le
    {R : Type u} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (p : Ideal R) [p.IsPrime]
    (q : PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) :
    c ≤ n := by
  sorry



end Algebra
