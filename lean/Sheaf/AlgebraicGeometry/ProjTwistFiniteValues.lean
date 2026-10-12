module
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Module.LocalizedModule.Basic
@[expose] public section
universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj
/-- Finite representatives satisfy the section values for every canonical evaluation.
Source: Stacks Project, Section 27.8, Lemma 27.8.1 (finite standard-open refinements)
and the construction preceding Lemma 27.8.4, Tag 01M7, applied to A(k).
(blueprint: new-finite-values)

Proof: write the section near each point as a homogeneous fraction a/d. Choose a
positive-degree homogeneous u whose basic open contains that point and is inside
this neighborhood and D₊(f). Replace the fraction by N/h, where N=a*u*f and h=d*u*f.
Then c=deg(h)>0, D₊(h) is inside that neighborhood, and the section there is N/h.
The chart D₊(f) ≅ Spec(B) carries D₊(h) to D(g), with g=h^b/f^c in B.
Quasi-compactness selects finitely many such opens covering D₊(f); their g's span
one, since their principal opens cover Spec(B). Enumerate them by Fin n. Define
z=h^(b-1)*N/f^c in M=A_f, and t=z/g in M localized at g. The identity
h^b/f^c=g shows this is N/h wherever h is invertible.

For any p and additive e with the two displayed identities, let x be 1/g in M_g.
Since g*x=1, scalar compatibility and e(1)=1 imply F(g)*e(x)=1. Thus F(g) is a
unit even though this is not a separate hypothesis. Since F(g)=h^b/f^c and f is
invertible at p, h is invertible there too, so p lies in D₊(h). Similarly g*t=z
implies F(g)*e(t)=F(z). Cancel this unit to obtain e(t)=N/h=s(p). This works for
every e, without assuming it is a ring map. If the chart is empty, B is the zero
ring: use n=0 and the empty family (its span is both bottom and top). The
construction allows zero sections, nilpotent f, degree-zero d, and negative k. -/
theorem twist_finiteLocal_values
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (hspan : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      ∀ (i : Fin n) (p : basicOpen 𝒜 f)
        (e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
          IsLocalization.map (M := Submonoid.powers f)
            (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
            (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
            (Submonoid.powers_le.mpr p.2) z) →
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) =
            IsLocalization.map (M := Submonoid.powers f)
              (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
              (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
              (Submonoid.powers_le.mpr p.2)
              (algebraMap B (Localization.Away f) a) * e x) →
        e (t i) = (s.1 p).1 := by
  sorry
end AlgebraicGeometry.Proj
