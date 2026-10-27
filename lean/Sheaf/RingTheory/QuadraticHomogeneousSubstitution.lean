module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Homogeneous substitution for a quadratic formal cone

Source: Stacks Project, curves.tex, Tag 0C4A (lemma-2-branches-delta-1),
proof of (1) implies (2), Cases I and II, with coordinates interchanged in Case II.
(blueprint: lem-sfb-quadratic-homogeneous-substitution)

The coefficient formula specifies the substitution without choosing an unspecified map.
The equality binders for `r` and `q` name the displayed polynomial and homogeneous equation.
-/

@[expose] public section

universe u

namespace QuadraticSeries

/-- Homogeneous substitution has the quadratic kernel and scalar-constant image.
Source: Stacks Project, curves.tex, Tag 0C4A (lemma-2-branches-delta-1), Cases I and II.
(blueprint: lem-sfb-quadratic-homogeneous-substitution)

Proof plan:
1. Since a is invertible, r = a*(Z²+(b/a)Z+c/a), and the two principal ideals agree
   (def-weil-pbc-algebra-hom-quotient). The monic quadratic quotient has basis 1,z by
   AdjoinRoot.powerBasis' (lem-weil-pbc-monic-quotient-free). This basis gives injectivity
   of the scalar map (def-weil-pbc-free-module); the quotient relation gives z²=-(b/a)z-c/a.
2. The coefficient of t^n is the finite evaluation of the homogeneous part H_n at (z,1).
   Finite convolution proves multiplicativity and the algebra identities, with X mapping
   to zt and Y to t (def-weil-polynomial-ring, def-weil-pbc-multivariate-power-series).
3. Divide each homogeneous polynomial by Q=X²+(b/a)XY+(c/a)Y², eliminating decreasing
   X exponents: H_n=Q*G_(n-2)+u_n*Y^n+v_n*X*Y^(n-1). Treat n=0,1 separately.
4. If its evaluation vanishes, independence of 1,z makes u_n and v_n zero. Assemble the
   G_m coefficientwise to obtain H=QG=q*(a⁻¹G). Conversely the relation makes phi(q)=0.
   Thus ker(phi)=(q) (lem-weil-pbc-monic-quotient-free and the preceding definitions).
5. Constants in the image are scalar. Every scalar-constant series has coefficients
   alpha_n+delta_n*z by the basis; the explicit lift has only Y^n and X*Y^(n-1) terms.
   Its coefficient formula gives the desired series, proving image(phi)=F+tB.
6. The quotient universal property gives j([H])=phi(H), and the kernel calculation makes
   j injective with the same image (def-weil-pbc-algebra-hom-quotient). Scalar series and
   tB have scalar constant coefficient. None of these steps uses a discriminant condition.
-/
theorem homogeneous_substitution (F : Type u) [Field F] (a b c : F) (ha : a ≠ 0)
    (r : Polynomial F)
    (hr : r = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c)
    (q : MvPowerSeries (Fin 2) F)
    (hq : q = MvPowerSeries.C a * MvPowerSeries.X 0 ^ 2 +
      MvPowerSeries.C b * MvPowerSeries.X 0 * MvPowerSeries.X 1 +
      MvPowerSeries.C c * MvPowerSeries.X 1 ^ 2) :
    Ideal.span {r} = Ideal.span
      {Polynomial.X ^ 2 + Polynomial.C (b / a) * Polynomial.X + Polynomial.C (c / a)} ∧
    Function.Injective (algebraMap F (AdjoinRoot r)) ∧
    (∃ e : Module.Basis (Fin 2) F (AdjoinRoot r), e 0 = 1 ∧ e 1 = AdjoinRoot.root r) ∧
    AdjoinRoot.root r ^ 2 =
      -algebraMap F (AdjoinRoot r) (b / a) * AdjoinRoot.root r -
        algebraMap F (AdjoinRoot r) (c / a) ∧
    ∃ φ : MvPowerSeries (Fin 2) F →ₐ[F] PowerSeries (AdjoinRoot r),
      (∀ (H : MvPowerSeries (Fin 2) F) (n : ℕ),
        PowerSeries.coeff n (φ H) =
          ∑ i ∈ Finset.range (n + 1),
            algebraMap F (AdjoinRoot r)
              (MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 (n - i)) H) *
                AdjoinRoot.root r ^ i) ∧
      φ (MvPowerSeries.X 0) = PowerSeries.C (AdjoinRoot.root r) * PowerSeries.X ∧
      φ (MvPowerSeries.X 1) = PowerSeries.X ∧
      RingHom.ker φ.toRingHom = Ideal.span {q} ∧
      (∀ h : PowerSeries (AdjoinRoot r),
        (∃ H, φ H = h) ↔ ∃ d : F, ∃ g : PowerSeries (AdjoinRoot r),
          h = PowerSeries.C (algebraMap F (AdjoinRoot r) d) + PowerSeries.X * g) ∧
      (∃ j : (MvPowerSeries (Fin 2) F ⧸ Ideal.span {q}) →ₐ[F] PowerSeries (AdjoinRoot r),
        (∀ H : MvPowerSeries (Fin 2) F, j (Ideal.Quotient.mk (Ideal.span {q}) H) = φ H) ∧
        Function.Injective j ∧
        (∀ h : PowerSeries (AdjoinRoot r), (∃ v, j v = h) ↔ ∃ H, φ H = h)) ∧
      (∀ f : PowerSeries F,
        ∃ H, φ H = PowerSeries.map (algebraMap F (AdjoinRoot r)) f) ∧
      (∀ g : PowerSeries (AdjoinRoot r), ∃ H, φ H = PowerSeries.X * g) ∧
      (∀ α δ : ℕ → F,
        φ (fun d : Fin 2 →₀ ℕ ↦
          if d 0 = 0 then α (d 1) else if d 0 = 1 then δ (d 1 + 1) else 0) =
        PowerSeries.mk (fun n : ℕ ↦
          if n = 0 then algebraMap F (AdjoinRoot r) (α 0)
          else algebraMap F (AdjoinRoot r) (α n) +
            algebraMap F (AdjoinRoot r) (δ n) * AdjoinRoot.root r)) := by
  sorry

end QuadraticSeries
