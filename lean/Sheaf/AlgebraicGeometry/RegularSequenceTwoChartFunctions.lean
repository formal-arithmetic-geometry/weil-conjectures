module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.RegularSequencePowers

/-!
# Functions on a two-chart scheme and a regular sequence

Source: Stacks Project, Algebra, Tag 07DV; Resolution of Surfaces, Tag 0AGS(4), `n = 0`,
generalized by the explicit two-chart divisibility and sheaf gluing argument
(blueprint: lem-sfb-regular-sequence-two-chart-functions).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The coefficient map is a ring isomorphism for the specified two-chart scheme; every
positive-denominator representation of a global section has a unique common coefficient.
Source: Stacks Project, Algebra, Tag 07DV, and Resolution of Surfaces, Tag 0AGS(4), `n = 0`
(blueprint: lem-sfb-regular-sequence-two-chart-functions).

Proof: write the chart values of a global section as `a/s^r` and `b/t^n`, increasing zero
exponents to one. Their restrictions agree, so the overlap hypothesis makes their images in
`A[1/(s*t)]` equal. Clear denominators there and use the localization equality criterion and
domain cancellation to get `t^n*a = s^r*b` in `A`. The positive-powers theorem
`RingTheory.Sequence.isRegular_ofFn_pow_iff` (lem-weil-pbc-regular-sequence-powers) says
`(s^r,t^n)` is regular. Thus multiplication by `t^n` on `A/(s^r)` is injective, so
`a = s^r*e` for some `e`. Cancel `s^r` to get `b = t^n*e`; the same cancellation proves
uniqueness of `e`. Compatibility of the chart embeddings with `q` identifies the chart
values with those of the coefficient section of `e`. Injectivity on both charts and sheaf
uniqueness on their cover give the asserted global equality, hence surjectivity. To prove
injectivity, restrict equal coefficient sections to `U`, embed into `A[1/s]`, and cancel a
power of the nonzero `s` using the localization equality criterion. A bijective unital ring
homomorphism is a ring isomorphism. -/
theorem regularSequence_twoChart_functions
    {A : Type u} [CommRing A] [IsDomain A] (s t : A)
    (hs : s ≠ 0) (ht : t ≠ 0) (hreg : RingTheory.Sequence.IsRegular A [s, t])
    (Z : Scheme.{u}) (q : Z ⟶ Spec (CommRingCat.of A))
    (U V : Z.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    (iU : Γ(Z, U) →+* Localization.Away s) (iV : Γ(Z, V) →+* Localization.Away t)
    (hiU : Function.Injective iU) (hiV : Function.Injective iV)
    (hAU : ∀ e : A,
      iU (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) e)) =
          algebraMap A (Localization.Away s) e)
    (hAV : ∀ e : A,
      iV (Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) e)) =
          algebraMap A (Localization.Away t) e)
    (hoverlap : ∀ (c : Γ(Z, U)) (d : Γ(Z, V)),
      Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op c =
        Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op d →
      (IsLocalization.Away.awayToAwayRight s t :
        Localization.Away s →+* Localization.Away (s * t)) (iU c) =
      (IsLocalization.Away.awayToAwayLeft t s :
        Localization.Away t →+* Localization.Away (s * t)) (iV d)) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) ∧
      ∀ (v : Γ(Z, ⊤)) (a b : A) (r n : ℕ), 1 ≤ r → 1 ≤ n →
        iU (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v) =
          IsLocalization.mk' (M := Submonoid.powers s) (Localization.Away s)
            a ⟨s ^ r, ⟨r, rfl⟩⟩ →
        iV (Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op v) =
          IsLocalization.mk' (M := Submonoid.powers t) (Localization.Away t)
            b ⟨t ^ n, ⟨n, rfl⟩⟩ →
        ∃! e : A, a = s ^ r * e ∧ b = t ^ n * e ∧
          v = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appTop) e := by
  sorry

end AlgebraicGeometry
