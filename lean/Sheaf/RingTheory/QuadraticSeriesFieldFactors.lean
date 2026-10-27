module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.Field.IsField
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.PowerSeriesNormalDomain

/-!
# Field factors of a quadratic coefficient series algebra

Source: Stacks Project, curves.tex, Tag 0C4A (lemma-2-branches-delta-1),
proof of (1) implies (2), Cases I and II; algebra.tex, Tag 0BI0.
(blueprint: lem-sfb-quadratic-series-field-factors)

The polynomial parameter is fixed by an equality, and its coefficient algebra is
Mathlib's quotient `AdjoinRoot p`. The auxiliary subring is the displayed ring A:
series whose constant coefficient belongs to the scalar field. The theorem also
identifies it with F+tB. No field structure is imposed on the quadratic quotient.
-/

@[expose] public section

noncomputable section

universe u

namespace QuadraticSeries

/-- The ring A = F+tB, represented by the inverse image of the scalar subring under
constant coefficient. The equality with F+tB is included in `field_factors`.
Source: Stacks 0C4A, Cases I and II, and its displayed constant-coefficient description.
(blueprint: lem-sfb-quadratic-series-field-factors) -/
abbrev scalarConstantSubring {F : Type u} [Field F] (p : Polynomial F) :
    Subring (PowerSeries (AdjoinRoot p)) :=
  (algebraMap F (AdjoinRoot p)).range.comap PowerSeries.constantCoeff

/-- Field factors, normality, and the quadratic integral equation for B over A.
Source: Stacks 0C4A (lemma-2-branches-delta-1), Cases I and II; normality from 0BI0.
(blueprint: lem-sfb-quadratic-series-field-factors)

Proof following the eight steps of the node:
1. The monic-quotient basis theorem (lem-weil-pbc-monic-quotient-free,
   `AdjoinRoot.powerBasis'`) gives the basis 1,z, dimension two, and
   z² = -βz-γ. In particular the scalar field embeds.
2. For a root r, put s=-β-r. Then rs=γ and (r-s)²=β²-4γ, so r≠s.
   Evaluation sends a+bz to (a+br,a+bs). Its inverse sends (c,d) to
   (rd-sc)/(r-s) + ((c-d)/(r-s))z; substitution verifies both identities.
3. In the absence of roots, the norm N=a²-βab+γb² of a+bz≠0 is nonzero:
   if b=0 this is a²; otherwise N=b²p(-a/b). Multiplication by
   a-βb-bz gives N, hence division by N supplies an inverse. Thus L is a
   degree-two field. Choose one field factor here and two copies of F when split.
4. Extend the coefficient algebra isomorphism coefficientwise to series, with
   inverse obtained by applying its inverse to each tuple of coefficients.
   Finite Cauchy sums prove multiplicativity; t goes to the tuple of variables.
5. Fields are Noetherian normal domains. Apply
   lem-weil-pbc-power-series-normal-domain (0BI0) to every field factor.
   A nilpotent has zero image in each domain, hence is zero in B.
6. Expand every coefficient in the basis 1,z to obtain the unique series u,v.
   The scalar series map is injective coefficientwise. The identity
   u=C(u₀)+t*sum(u_(n+1)t^n) puts scalar series in A and identifies A=F+tB.
7. Expand (u+zv)(u-βv-zv)=u²-βuv+γv² using the relation for z.
   The second factor is 2u-βv-h, giving the displayed monic equation.
   Its coefficients lie in A, so every h is integral over A. The expression
   h=u*1+v*z also gives the two module generators and Module.Finite.
8. Multiplication by t shifts coefficients, and is injective on B; its
   restriction to A is injective as well. None of these arguments divides by two.
-/
theorem field_factors (F : Type u) [Field F] (β γ : F) (p : Polynomial F)
    (hp : p = Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ)
    (hdisc : β ^ 2 - 4 * γ ≠ 0) :
    (∀ r : F, p.eval r = 0 →
      p.eval (-β - r) = 0 ∧ r ≠ -β - r ∧
        ∃ e : AdjoinRoot p ≃ₐ[F] F × F,
          ∀ q : Polynomial F, e (AdjoinRoot.mk p q) = (q.eval r, q.eval (-β - r))) ∧
    ((¬ ∃ r : F, p.eval r = 0) →
      IsField (AdjoinRoot p) ∧ Module.finrank F (AdjoinRoot p) = 2) ∧
    (∃ m : ℕ, (m = 1 ∨ m = 2) ∧
      ∃ (K : Fin m → Type u) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)),
        ∃ (φ : AdjoinRoot p ≃ₐ[F] (∀ i, K i))
          (Φ : PowerSeries (AdjoinRoot p) ≃ₐ[F] (∀ i, PowerSeries (K i))),
          (∀ (h : PowerSeries (AdjoinRoot p)) (i : Fin m) (n : ℕ),
            PowerSeries.coeff n (Φ h i) = φ (PowerSeries.coeff n h) i) ∧
          Φ PowerSeries.X = (fun i ↦ (PowerSeries.X : PowerSeries (K i))) ∧
          ∀ i : Fin m, IsDomain (PowerSeries (K i)) ∧
            IsIntegrallyClosed (PowerSeries (K i))) ∧
    IsReduced (PowerSeries (AdjoinRoot p)) ∧
    (∀ h : PowerSeries (AdjoinRoot p), h ∈ scalarConstantSubring p ↔
      ∃ (a : F) (g : PowerSeries (AdjoinRoot p)),
        h = PowerSeries.C (algebraMap F (AdjoinRoot p) a) + PowerSeries.X * g) ∧
    Function.Injective (PowerSeries.map (algebraMap F (AdjoinRoot p))) ∧
    (∀ u : PowerSeries F,
      PowerSeries.map (algebraMap F (AdjoinRoot p)) u ∈ scalarConstantSubring p) ∧
    (∀ h : PowerSeries (AdjoinRoot p), ∃ u v : PowerSeries F,
      h = PowerSeries.map (algebraMap F (AdjoinRoot p)) u +
        PowerSeries.C (AdjoinRoot.root p) * PowerSeries.map (algebraMap F (AdjoinRoot p)) v ∧
      (∀ u' v' : PowerSeries F,
        h = PowerSeries.map (algebraMap F (AdjoinRoot p)) u' +
          PowerSeries.C (AdjoinRoot.root p) * PowerSeries.map (algebraMap F (AdjoinRoot p)) v' →
        u' = u ∧ v' = v) ∧
      h ^ 2 +
        (PowerSeries.C (algebraMap F (AdjoinRoot p) β) *
          PowerSeries.map (algebraMap F (AdjoinRoot p)) v -
          2 * PowerSeries.map (algebraMap F (AdjoinRoot p)) u) * h +
        (PowerSeries.map (algebraMap F (AdjoinRoot p)) u ^ 2 -
          PowerSeries.C (algebraMap F (AdjoinRoot p) β) *
            PowerSeries.map (algebraMap F (AdjoinRoot p)) u *
            PowerSeries.map (algebraMap F (AdjoinRoot p)) v +
          PowerSeries.C (algebraMap F (AdjoinRoot p) γ) *
            PowerSeries.map (algebraMap F (AdjoinRoot p)) v ^ 2) = 0) ∧
    Submodule.span (scalarConstantSubring p)
      ({1, PowerSeries.C (AdjoinRoot.root p)} : Set (PowerSeries (AdjoinRoot p))) = ⊤ ∧
    Module.Finite (scalarConstantSubring p) (PowerSeries (AdjoinRoot p)) ∧
    (∀ h : PowerSeries (AdjoinRoot p), IsIntegral (scalarConstantSubring p) h) ∧
    PowerSeries.X ∈ scalarConstantSubring p ∧
    Function.Injective (fun h : PowerSeries (AdjoinRoot p) ↦ PowerSeries.X * h) ∧
    Function.Injective (fun h : scalarConstantSubring p ↦
      PowerSeries.X * (h : PowerSeries (AdjoinRoot p))) := by
  sorry

end QuadraticSeries
