/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Sheaf.RingTheory.RelativeGlobalCompleteIntersectionSmoothJacobian

/-!
# A Jacobian minor from a smooth fibre of a localized presentation

Source: Stacks Project, Algebra, proof of Lemma 00TF, applying Lemma 00TE to the fibre.
(blueprint: lem-weil-pbc-smooth-fibre-localized-presentation-jacobian).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A smooth fibre at a prime supplies a maximal Jacobian minor of any relative global
complete intersection presentation of a principal neighbourhood, avoiding the lifted prime.
Source: Stacks Project, Algebra, proof of Lemma 00TF, and Lemma 00TE.
(blueprint: lem-weil-pbc-smooth-fibre-localized-presentation-jacobian).

Proof:
1. Put `p = q ∩ R`, `k = κ(p)` and `T = R[x]/(f)`. Tensor the given algebra equivalence
   with `k`. Localization commutes with tensor product, so the fibre of `T` is the
   localization of `p.Fiber S` at the image of `g`. The equality of contracted primes
   identifies the prime of this localization over `q` with the fibre prime over
   `comap e.symm qg`. This follows also by composing both maps with `κ(q)` and comparing
   their kernels; the residue fields of the corresponding localized primes agree.
2. Choose a smooth principal neighbourhood `F_h` of the original fibre prime. The image
   of `g` avoids that prime. The two iterated localizations at `g` and `h` agree with
   `F_(g*h)`, and localizing a smooth algebra is smooth. Transporting through the
   fibre equivalence proves smoothness of the fibre of `T` at its corresponding prime.
3. Polynomial scalar extension and tensoring a quotient identify this fibre with
   `k[x]/(map (algebraMap R k) ∘ f)`. It is nonzero because it has that prime. The relative
   complete intersection condition gives its dimension `n-c` and `c ≤ n`. Over the field
   `k`, whose only prime is zero with residue field `k`, this is a relative global
   complete intersection presentation in its own right.
4. Apply the forward implication of the Jacobian criterion 00TE to this fibre
   presentation: some strictly increasing `i : Fin c → Fin n` gives a minor outside
   the fibre prime. Coefficient reduction commutes with partial derivatives (verify
   on monomials) and with determinants (the Leibniz formula), hence that minor is
   the image of the displayed minor of `f`.
5. The fibre prime is the kernel of the map to the residue field of `comap e.symm qg`.
   An element `t ⊗ 1` lies in this kernel exactly when `t` lies in that prime. Thus the
   original minor avoids `comap e.symm qg`, as required. This includes `c = 0`, when
   the empty determinant is one; if `c > n`, the nonempty fibre already contradicts
   the relative complete intersection dimension condition. -/
theorem exists_jacobian_minor_of_smooth_fibre_localizedPresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (g : S)
    (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q)
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (hci : IsRelativeGlobalCompleteIntersectionPresentation f)
    (e : Localization.Away g ≃ₐ[R]
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hsmooth : IsSmoothAtPrime (q.comap (algebraMap R S)).asIdeal.ResidueField
      (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩)) :
    ∃ i : Fin c → Fin n, StrictMono i ∧
      Ideal.Quotient.mk (Ideal.span (Set.range f))
        (Matrix.det (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j))) ∉
          (PrimeSpectrum.comap e.symm.toRingHom qg).asIdeal := by sorry

end Algebra
