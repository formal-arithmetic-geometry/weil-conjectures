module

public import WeilConjectures.ZetaSeries
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration

/-!
# Prime-to-ell residue degree after arbitrary field extension

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf,
Expose II Proposition 1.2.7, printed pp. 25--26
(blueprint: lem-per-prime-to-ell-residue-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- For a finite field extension `L/k` of degree `d` prime to `ell`, every point of
`Spec L ×_{Spec k} Spec K` has finite residue degree over `K`, and one residue degree
is prime to `ell`, for every field extension `K/k`. This is the field-theoretic
assertion of ILO, Exposé II, Proposition 1.2.7.
(blueprint: lem-per-prime-to-ell-residue-base-change)

Proof:
1. The affine fibre-product isomorphism (lem-weil-pbc-fibre-product-affine-spectra)
identifies `P` with the spectrum of `A = L ⊗[k] K`, over `Spec K`. The point and
residue-field comparisons (lem-weil-pbc-fibre-product-points and
lem-weil-pbc-fibre-product-point-residue-field) identify its points with primes of
`A` and their residue fields with the fraction fields of the prime quotients.
2. A `k`-basis of `L` gives a `K`-basis `e_i ⊗ 1` of `A`: the tensor relations give
spanning, and the scalar-extended coordinate maps give independence. Thus its
`K`-dimension is `d > 0` (def-weil-pbc-module-tensor-product and
 def-weil-vector-space-dimension).
3. Every prime quotient is a nonzero finite-dimensional domain and hence a field
(lem-weil-pbc-finite-dimensional-domain-is-field). It is the corresponding residue
field as a `K`-extension, proving finiteness of every residue degree.
4. The algebra is Artinian (lem-weil-pbc-finite-dim-algebra-artinian). Filter its unit
ideal by ideals with simple successive quotients
(lem-weil-pbc-artinian-ideal-length-one-filtration).
5. A nonzero element of each simple quotient generates it, identifying it with
`A / m` for its maximal annihilator `m`, compatibly with the `K`-action. Its
`K`-dimension is consequently the residue degree of the point associated to `m`.
6. Additivity of dimension along the filtration expresses `d` as the sum of these
residue degrees, with repetitions allowed. Since `ell` does not divide `d`, it
cannot divide every summand. This gives the required point, including when `A` is
nonreduced. -/
theorem prime_to_ell_residue_base_change
    {k L K : Type u} [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [FiniteDimensional k L]
    (d ell : ℕ) (hd : Module.finrank k L = d) (hell : Nat.Prime ell)
    (hcop : ¬ ell ∣ d) :
    (∀ z : pullback (C := Scheme)
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      ((pullback.snd (C := Scheme)
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldAlgebraMap z).Finite) ∧
      ∃ z : pullback (C := Scheme)
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        ¬ ell ∣
          (pullback.snd (C := Scheme)
            (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).degreeOver z := by
  sorry

end AlgebraicGeometry
