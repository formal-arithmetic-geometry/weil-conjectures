module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Rational local coordinates in a Tate algebra

Source: Conrad, Several approaches to non-archimedean geometry, Theorem 1.1.5(1)
and Exercise 1.2.8(4), and the first-order Taylor consequence
(blueprint: lem-per-tate-rational-local-coordinates).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace RestrictedSeries

/-- Evaluation of a formal series by its coefficient sum. On the restricted-series ring,
the theorem below asserts convergence at every point of the closed unit polydisc.
Source: Conrad, Exercise 1.2.8(4)
(blueprint: lem-per-tate-rational-local-coordinates). -/
noncomputable def rationalValue {F : Type u} [NormedField F] {r : ℕ}
    (a : Fin r → F) (f : MvPowerSeries (Fin r) F) : F :=
  ∑' ν : Fin r →₀ ℕ, MvPowerSeries.coeff ν f * ν.prod (fun i n ↦ a i ^ n)

/-- The coordinate difference `x_i - a_i` in the existing restricted-series subring.
Source: Conrad, Exercise 1.2.8(4)
(blueprint: lem-per-tate-rational-local-coordinates). -/
noncomputable def rationalCoordinate {F : Type u} [NormedField F] [IsUltrametricDist F]
    {r : ℕ} (a : Fin r → F) (i : Fin r) :
    MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ)) :=
  ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_monomial _ _ _⟩ - constants F r (a i)

/-- The canonical scalar structure on a localization of the restricted-series ring.
It is the composite of the existing constant-series map and the localization map.
Source: Conrad, Theorem 1.1.5(1)
(blueprint: lem-per-tate-rational-local-coordinates). -/
noncomputable instance rationalLocalAlgebra {F : Type u} [NormedField F]
    [IsUltrametricDist F] {r : ℕ}
    (q : Ideal (MvPowerSeries.IsRestricted.subring (R := F)
      (fun _ : Fin r ↦ (1 : ℝ)))) [q.IsPrime] :
    Algebra F (Localization.AtPrime q) :=
  ((algebraMap _ (Localization.AtPrime q)).comp (constants F r)).toAlgebra

/-- The rational Tate local ring is regular, with derivative coordinates on its cotangent
space. Evaluation is specified by `HasSum`, so the ring map is canonical, including at
points on the boundary of the unit polydisc. The residue and cotangent maps are likewise
specified on every fraction, rather than chosen without their normalization.

Source: Conrad, Theorem 1.1.5(1), Exercise 1.2.8(4), and their first-order Taylor consequence
(blueprint: lem-per-tate-rational-local-coordinates).

Proof plan:
1. Gauss completeness and bounded substitution give inverse translations `x = t + a`
   and `t = x - a` (lem-trf-restricted-series-gauss-completion,
   lem-per-tate-banach-substitution). Evaluation becomes the constant coefficient.
2. Partition every nonconstant monomial by its first nonzero coordinate. This gives
   generators `x_i-a_i` of the kernel. Constants prove surjectivity and maximality.
   Evaluation of fractions is well defined, surjective, and has kernel `qR`.
3. The zero-ideal case of lem-trf-affinoid-polynomial-closed-point-comparison gives
   Noetherianity. Localize generators of ideals; the local dimension bound gives dim <= r.
4. The successive coordinate ideals are prime, by the lowest homogeneous part argument.
   Their strict chain survives localization, giving dim >= r and regularity.
5. Natural-number coefficients have norm at most one. Termwise differentiation therefore
   preserves restrictedness and commutes with polynomial approximation and translation.
   The first-order coefficients satisfy Leibniz and send each coordinate to a standard vector.
6. Map to `F ⊕ F^r` with square-zero second summand. Denominators outside the kernel map
   to units. Localizing and passing to `m/m²` gives the displayed fraction formula.
7. The coordinate classes span modulo `m²`; derivative coordinates and the stated sum
   are inverse. For r=0 the ring and localization are F and the cotangent space is zero.
-/
theorem tate_rational_local_coordinates
    (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (hF : ∃ c : F, c ≠ 0 ∧ ‖c‖ ≠ 1) (r : ℕ)
    (a : Fin r → F) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∃ (ev : (MvPowerSeries.IsRestricted.subring (R := F)
        (fun _ : Fin r ↦ (1 : ℝ))) →+* F)
      (_ : (RingHom.ker ev).IsMaximal),
      (∀ f, HasSum (fun ν : Fin r →₀ ℕ ↦
        MvPowerSeries.coeff ν f.val * ν.prod (fun i n ↦ a i ^ n)) (ev f)) ∧
      (∀ (f : MvPowerSeries.IsRestricted.subring (R := F)
          (fun _ : Fin r ↦ (1 : ℝ))) (i : Fin r),
        MvPowerSeries.IsRestricted (fun _ : Fin r ↦ (1 : ℝ))
          (MvPowerSeries.pderiv F i f.val)) ∧
      RingHom.ker ev = Ideal.span (Set.range (rationalCoordinate a)) ∧
      IsRegularLocalRing (Localization.AtPrime (RingHom.ker ev)) ∧
      ∃ (ρ : Localization.AtPrime (RingHom.ker ev) →+* F),
        Function.Surjective ρ ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker ev)) ∧
        (∀ (h : MvPowerSeries.IsRestricted.subring (R := F)
            (fun _ : Fin r ↦ (1 : ℝ))) (v : (RingHom.ker ev).primeCompl),
          ρ (Localization.mk h v) = ev h / ev v.val) ∧
        (r = 0 → Function.Bijective ρ) ∧
        ∃ (hy : ∀ i, algebraMap _ (Localization.AtPrime (RingHom.ker ev))
            (rationalCoordinate a i) ∈ IsLocalRing.maximalIdeal
              (Localization.AtPrime (RingHom.ker ev)))
          (θ : (IsLocalRing.maximalIdeal
            (Localization.AtPrime (RingHom.ker ev))).Cotangent ≃ₗ[F] (Fin r → F)),
          (∀ (h : MvPowerSeries.IsRestricted.subring (R := F)
              (fun _ : Fin r ↦ (1 : ℝ))) (v : (RingHom.ker ev).primeCompl)
              (hm : Localization.mk h v ∈ IsLocalRing.maximalIdeal
                (Localization.AtPrime (RingHom.ker ev))),
            ev h = 0 → ∀ i,
              θ ((IsLocalRing.maximalIdeal _).toCotangent ⟨Localization.mk h v, hm⟩) i =
                rationalValue a (MvPowerSeries.pderiv F i h.val) / ev v.val) ∧
          (∀ b : Fin r → F,
            θ.symm b = ∑ i, b i • (IsLocalRing.maximalIdeal _).toCotangent
              ⟨algebraMap _ (Localization.AtPrime (RingHom.ker ev))
                (rationalCoordinate a i), hy i⟩) := by
  sorry

end RestrictedSeries
