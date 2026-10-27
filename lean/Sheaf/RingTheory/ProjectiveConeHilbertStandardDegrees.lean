/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Projective charts and the Hilbert function of the cone

Source: Hironaka, Certain numerical characters of singularities (1970), Lemma 8,
pp.160--162, (9.1)--(9.6), pp.162--164, and Remark (12.2), pp.167--168
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees).

The auxiliary definitions construct the numerical data introduced in this node.
The initial ideal is constructed in the published associated graded ring, using
the images of all elements of the ideal lying in each filtration step.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace Hironaka

/-- The intersection `C_d` of an ideal with the degree-`d` part of a graded algebra.
Source: Hironaka (1970), p.155 and Lemma 8
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
def gradedIdealPiece {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) (C : Ideal A) (d : ℕ) : Submodule k A :=
  𝒜 d ⊓ C.restrictScalars k

/-- The multiplicity of `d` among minimal homogeneous generator degrees:
`dim C_d / (sum_{j=1}^d A_j C_{d-j})`. The denominator is pulled back to `C_d`.
Source: Hironaka (1970), p.155, definition of the degree sequence
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def gradedGeneratorMultiplicity
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) (C : Ideal A) (d : ℕ) : ℕ :=
  Module.finrank k
    ((gradedIdealPiece 𝒜 C d) ⧸
      (Submodule.comap (gradedIdealPiece 𝒜 C d).subtype
        (∑ j ∈ Finset.Icc 1 d, 𝒜 j * gradedIdealPiece 𝒜 C (d - j))))

/-- Increasing enumeration of positive generator degrees with the given multiplicities,
padded by infinitely many infinities. Indexing starts at zero: entry `i` is the least
positive degree whose cumulative multiplicity exceeds `i`; the empty infimum is infinity.
Source: Hironaka (1970), p.155, conditions (i)--(ii)
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def generatorDegreeSequence (multiplicity : ℕ → ℕ) (i : ℕ) : ℕ∞ :=
  sInf {e : ℕ∞ | ∃ d : ℕ, e = (d : ℕ∞) ∧ 1 ≤ d ∧
    i < ∑ j ∈ Finset.Icc 1 d, multiplicity j}

/-- The degree-`d` subspace of the published associated graded ring, constructed as
the residue-field span of the canonical degree-`d` inclusion. Scalars preserve degree.
Source: Hironaka (1970), pp.153--155
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def adicGrade {W : Type u} [CommRing W] (l : Ideal W) (d : ℕ) :
    Submodule (W ⧸ l) (Ideal.associatedGraded l) :=
  Submodule.span (W ⧸ l)
    (Set.range (DirectSum.of (Ideal.associatedGradedPiece l) d))

/-- The initial ideal, equivalently the kernel of `gr_l W → gr_(l/c) (W/c)`
when `c ≤ l`. Its degree-`d` part consists of classes of elements of `c ∩ l^d`.
Taking every filtration degree includes the zero classes from higher-order elements.
Source: Hironaka (1970), p.154, initial ideals
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def adicInitialIdeal {W : Type u} [CommRing W] (l c : Ideal W) :
    Ideal (Ideal.associatedGraded l) :=
  Ideal.span {z | ∃ (d : ℕ) (a : (l ^ d : Ideal W)), a.val ∈ c ∧
    z = DirectSum.of (Ideal.associatedGradedPiece l) d (Submodule.Quotient.mk a)}

/-- The sequence `ν*(W,c)`, computed from the minimal homogeneous generator quotient
of the initial ideal in the published tangent cone. The scalar field is literally
`W / maximalIdeal W`. In the regular local applications all multiplicities are finite.
Source: Hironaka (1970), pp.154--155
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def nuStar {W : Type u} [CommRing W] [IsLocalRing W]
    (c : Ideal W) : ℕ → ℕ∞ :=
  letI : Field (W ⧸ IsLocalRing.maximalIdeal W) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal W)
  generatorDegreeSequence
    (gradedGeneratorMultiplicity (k := W ⧸ IsLocalRing.maximalIdeal W)
      (adicGrade (IsLocalRing.maximalIdeal W))
      (adicInitialIdeal (IsLocalRing.maximalIdeal W) c))

/-- The ideal `J` in the localized chart, generated by the dehomogenizations of
homogeneous elements of `C`; this constructs the actual ideal, not an arbitrary map.
Source: Hironaka (1970), Lemma 8 and pp.162--164
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def chartIdeal {k : Type u} [Field k] {r : ℕ}
    (C : Ideal (MvPolynomial (Option (Fin r)) k))
    (p : Ideal (MvPolynomial {j : Option (Fin r) // j ≠ none} k)) [p.IsPrime] :
    Ideal (Localization.AtPrime p) :=
  (Ideal.span {g | ∃ (d : ℕ) (f : MvPolynomial (Option (Fin r)) k),
    f ∈ C ∧ f.IsHomogeneous d ∧ g = MvPolynomial.dehomogenizeX k (none : Option (Fin r)) f}).map
      (algebraMap (MvPolynomial {j : Option (Fin r) // j ≠ none} k)
        (Localization.AtPrime p))

/-- The raw Hilbert--Samuel function of `W/c`, with maximal ideal the image of `l`.
In the theorem `c ≤ l` and `l` is the maximal ideal of a Noetherian local ring,
so these lengths are finite, and `toNat` loses no information.
Source: Hironaka (1970), p.155 and Lemma 8, p.161
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def quotientHilbertFunction {W : Type u} [CommRing W]
    (l c : Ideal W) (n : ℕ) : ℕ :=
  (Module.length (W ⧸ c)
    ((W ⧸ c) ⧸ (l.map (Ideal.Quotient.mk c)) ^ (n + 1))).toNat

/-- The cone's cumulative graded Hilbert function `sum_{j=0}^n dim_k (B/C)_j`,
using the canonical presentation `B_j / (C ∩ B_j)` of its degree-`j` part.
Source: Hironaka (1970), Lemma 8, pp.160--162
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees). -/
noncomputable def coneHilbertFunction {k : Type u} [Field k] {r : ℕ}
    (C : Ideal (MvPolynomial (Option (Fin r)) k)) : ℕ → ℕ :=
  AlgebraicGeometry.HilbertSamuel.summation (fun d =>
    Module.finrank k ((MvPolynomial.homogeneousSubmodule (Option (Fin r)) k d) ⧸
      (Submodule.comap (MvPolynomial.homogeneousSubmodule (Option (Fin r)) k d).subtype
        (C.restrictScalars k))))

/-- The projective chart's iterated Hilbert--Samuel function is bounded by the cone's
cumulative Hilbert function. Equality implies equality of the minimal tangent-ideal
generator degree sequences, including their infinite tails.

Source: Hironaka (1970), Lemma 8, pp.160--162, (9.1)--(9.6), pp.162--164,
Propositions 10--11 and Lemma 12, pp.164--167, and Remark (12.2), pp.167--168
(blueprint: lem-trf-projective-cone-hilbert-standard-degrees).

Proof (the node's six steps):
1. The polynomial-ring regularity leaf makes `Q` regular local. At a rational point,
shift homogeneous coordinates to put the point at the origin. A denominator with
nonzero constant term has its finite geometric-series inverse modulo `(u)^(n+1)`.
Thus the truncated local polynomial ring has the monomial basis of degree at most `n`.
2. Degree-`n` dehomogenization surjects onto `F/n^(n+1)` and kills `C_n`.
Length equals vector-space dimension at this rational point, by a composition series
refining the maximal-ideal filtration. Summing gives `Λ h_F ≤ h_S`.
3. If equality holds, differences give equality in every degree. Successively remove
the lowest nonzero homogeneous component of each dehomogenized element of `C`.
The jet-kernel equality puts its homogenization in `C`, so `C = H[X₀]`, where
`H = C ∩ k[X₁,...,X_r]`, and `J` is the localization of `H`.
4. The monomial description identifies the ambient associated graded ring with the
polynomial ring in the shifted variables and identifies its initial ideal with `H`.
Evaluation at `X₀ = 0` identifies the minimal generator quotients degree by degree.
5. For an arbitrary residue point, adjoin its residue coordinates one at a time.
The successive local rings are the localized scalar extensions at the evaluation
primes, with their actual dehomogenized ideals. Apply
`lem-trf-simple-residue-extension-hilbert-comparison` at each stage. The tower formula
`lem-kun-transcendence-degree-tower` makes the sum of the exponents equal to `δ`.
6. Scalar extension preserves graded dimensions and minimal-generator multiplicities.
Summation preserves inequalities, giving `Λ^(δ+1) h_F ≤ Λ h_final ≤ h_S`.
If the endpoints agree, a positive gap at any intermediate stage would persist under
every later summation. Hence each stage is an equality. The equality clause of
`lem-trf-simple-residue-extension-hilbert-comparison` transports `ν*` to the rational
case of step 4. The empty tower at `r = 0` is already that rational case. -/
theorem projectiveConeHilbertStandardDegrees
    {k : Type u} [Field k] (r : ℕ)
    (C : Ideal (MvPolynomial (Option (Fin r)) k))
    (hC : @Ideal.IsHomogeneous _ _ _ _ _ _
      (MvPolynomial.homogeneousSubmodule (Option (Fin r)) k) _ _
      (MvPolynomial.gradedAlgebra (σ := Option (Fin r)) (R := k)) C)
    (hCpos : C ≤ Ideal.span (Set.range (MvPolynomial.X :
      Option (Fin r) → MvPolynomial (Option (Fin r)) k)))
    (p : Ideal (MvPolynomial {j : Option (Fin r) // j ≠ none} k)) [p.IsPrime]
    (hp : ∀ (d : ℕ) (f : MvPolynomial (Option (Fin r)) k),
      f ∈ C → f.IsHomogeneous d → MvPolynomial.dehomogenizeX k (none : Option (Fin r)) f ∈ p) :
    IsRegularLocalRing (Localization.AtPrime p) ∧
    (∀ n : ℕ,
      ((AlgebraicGeometry.HilbertSamuel.summation^[
          Cardinal.toNat (Algebra.trdeg k p.ResidueField) + 1])
        (quotientHilbertFunction (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (chartIdeal C p))) n ≤ coneHilbertFunction C n) ∧
    ((AlgebraicGeometry.HilbertSamuel.summation^[
        Cardinal.toNat (Algebra.trdeg k p.ResidueField) + 1])
      (quotientHilbertFunction (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (chartIdeal C p)) = coneHilbertFunction C →
      nuStar (chartIdeal C p) =
        generatorDegreeSequence
          (gradedGeneratorMultiplicity
            (MvPolynomial.homogeneousSubmodule (Option (Fin r)) k) C)) := by
  sorry

end Hironaka
