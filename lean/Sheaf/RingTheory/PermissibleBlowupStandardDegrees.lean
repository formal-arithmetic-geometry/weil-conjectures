/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.RingTheory.PermissibleBasisChartData
public import Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import Mathlib.RingTheory.ReesAlgebra

/-! # Numerical nearness preserves tangent standard-basis degrees

Source: Hironaka, Certain numerical characters of singularities (1970),
Theorem III, p.156; degree sequences on p.155 and proof on p.187.
(blueprint: lem-trf-permissible-blowup-standard-degrees).

The blowup point is represented in its specified affine chart. Its local ring is
therefore the localization of that chart ring. The parameter presentation and the
kernel defining the transformed ideal reuse the published coordinate constructions.
The residue-field extension is the canonical map induced by the contraction equation;
using the residue field of the maximal prime identifies the base with `T / M`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Hironaka

open AlgebraicGeometry AlgebraicGeometry.AffineBlowup

/-- Numerical nearness implies equality of the padded tangent generator degree sequences.
`ρ` realizes the canonical chart quotient: its coefficient and ratio values are fixed by
`hρ`, so it is not an arbitrary comparison map. `hz` says that the chart point is over the
closed point of `T / b`. `LocalChart ρ z` is the specified `T'`, and `transformIdeal ρ z`
is the kernel of its actual map to the blowup local ring. The residue-field map in the
exponent is canonical, with base `κ(M)`, canonically identified with `T / M`.
All lengths are finite, and the residue extension has finite transcendence degree, so
both `toNat` conversions retain their values. `nuStar` uses the dimension of each minimal
generator quotient of the tangent initial ideal, with an infinite padded tail.

Source: Hironaka (1970), Theorem III, p.156, definition on p.155, proof on p.187.
(blueprint: lem-trf-permissible-blowup-standard-degrees).

Proof (the node's four steps):
1. Apply `lem-trf-normal-flat-double-initial-ideal` to identify the normal-cone fibre
with `B/C` and the tangent cone with `(B/C)[Y]`. The ambient tangent ideal is `C B[Y]`.
The graded-length bridge identifies the raw Hilbert function with the cumulative graded
one. Adding the `s` degree-one `Y` variables gives `h_R = Λ^s h_S`. Reduction modulo the
positive-degree ideal identifies the minimal-generator quotients of `C B[Y]` with those
of `C`, hence `ν*(T,b) = ν_B(C)` including multiplicities.
2. In the ambient local chart the distinct parameters `(x₀,y)` cut out
`Q = k[t₁,...,t_r]_p`, by the permissible-coordinate-chart theorem. Rees base change
identifies the closed exceptional fibre with `Proj S`, since its degree-d piece is
`I^d / m I^d`. Dehomogenizing its homogeneous equations gives `F = Q/J` and identifies
the image of the transform ideal with `J`. The fibre and the blowup point have the same
residue field, so their residue transcendence degree is the stated exponent `δ`.
3. The linear-section comparison gives `h_z ≤ Λ^(s+1) h_F`. The projective-cone
comparison gives `Λ^(δ+1) h_F ≤ h_S`. Summation preserves pointwise inequalities, so
`Λ^δ h_z ≤ Λ^(δ+s+1) h_F ≤ Λ^s h_S = h_R`. The hypothesis equates the endpoints,
forcing equality at every term. Inclusive summation is injective by successive differences;
cancel `Λ^δ` and `Λ^s` to obtain the two equality hypotheses of those comparisons.
4. Their equality clauses give `ν*(T',b') = ν*(Q,J) = ν_B(C) = ν*(T,b)`.
This is equality of whole sequences, including repeated degrees and infinite tails.
No converse is claimed. -/
theorem permissibleBlowupStandardDegrees
    {T : Type u} [CommRing T] [IsRegularLocalRing T]
    (r s : ℕ) (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (b : Ideal T) (hb : b ≤ Ideal.span (Set.range x))
    (hflat : Module.Flat
      ((T ⧸ b) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
      (Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))))
    (hred : IsReduced (T ⧸ b))
    (hmin : ∀ q ∈ minimalPrimes (T ⧸ b),
      ¬ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk b) ≤ q)
    (ρ : ParameterChart x →+*
      chartRing ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
        (Ideal.Quotient.mk b (x 0))) (hρ : IsQuotientChartMap x b ρ)
    (z : PrimeSpectrum (chartRing ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
      (Ideal.Quotient.mk b (x 0))))
    (hz : z.asIdeal.comap ((algebraMap (T ⧸ b) _).comp (Ideal.Quotient.mk b)) =
      IsLocalRing.maximalIdeal T)
    [IsRegularLocalRing (LocalChart ρ z)]
    (hnear :
      (HilbertSamuel.summation^[Cardinal.toNat
        (@Algebra.trdeg (IsLocalRing.maximalIdeal T).ResidueField z.asIdeal.ResidueField
          _ _ (Ideal.ResidueField.map (IsLocalRing.maximalIdeal T) z.asIdeal
            ((algebraMap (T ⧸ b) _).comp (Ideal.Quotient.mk b)) hz.symm).toAlgebra)])
        (fun n : ℕ => (Module.length (Localization.AtPrime z.asIdeal)
          ((Localization.AtPrime z.asIdeal) ⧸
            IsLocalRing.maximalIdeal (Localization.AtPrime z.asIdeal) ^ (n + 1))).toNat) =
      quotientHilbertFunction (IsLocalRing.maximalIdeal T) b) :
    nuStar (transformIdeal ρ z) = nuStar b := by
  sorry

end Hironaka
