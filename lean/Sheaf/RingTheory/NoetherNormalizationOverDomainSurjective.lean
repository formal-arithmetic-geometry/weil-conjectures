module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra.FiniteType

/-- The constructive part of Noether normalization over a domain, producing a surjective
localization map.  Source: Stacks Project, Algebra, Lemma 07NA.
(blueprint: new-noether-normalization-over-domain-surjective)
Proof: localize `S` at the nonzero elements of `R` and apply field Noether normalization to
the resulting finite-type algebra.  Rescale the normalized coordinates by denominators so that
they lie in `S`; injectivity over the fraction field then gives injectivity of evaluation over
`R`.  Express finite-integral equations for a finite set of algebra generators, clear their
coefficient denominators, and multiply by one common nonzero element of `R` so that the
equations hold in `S`.  If `f` is the product of these clearing factors, let `S'` be generated
over `R` by the normalized coordinates and by `f` times the original generators.  Rescaling
each monic equation shows that these generators are integral over the polynomial subalgebra,
so `S'` is finite over it.  Finally, every element of `S` is a polynomial in the original
generators; multiplying by a sufficiently large power of `f` rewrites it as a polynomial in
the generators of `S'`.  Hence every fraction in `S_f` comes from `S'_f`, which is precisely
surjectivity of the displayed localization map. -/
theorem exists_finite_subalgebra_away_surjective
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ (d : ℕ) (y : Fin d → S) (S' : Subalgebra R S),
      Function.Injective (MvPolynomial.aeval (R := R) y) ∧
      ∃ h : (MvPolynomial.aeval (R := R) y).range ≤ S',
        (letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
         Module.Finite (MvPolynomial.aeval (R := R) y).range S') ∧
        ∃ f : R, f ≠ 0 ∧
          Function.Surjective
            (IsLocalization.Away.map
              (Localization.Away (algebraMap R S' f))
              (Localization.Away (S'.val (algebraMap R S' f)))
              S'.val.toRingHom (algebraMap R S' f)) := by
  sorry

end Algebra.FiniteType
