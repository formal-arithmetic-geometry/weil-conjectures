module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Valuation.ValuationRing
import Sheaf.AlgebraicGeometry.FibreCartierLocal
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme

/-!
# Zero locus over a valuation base

Source: More on Morphisms, Lemma 37.33.3 (Tag 0EX8), with Divisors Lemma 31.19.9
(Tag 062Y) (blueprint: lem-sc-valuation-zero-section-relative-cartier).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
namespace Scheme
namespace Modules

/-- The zero scheme of a section whose restriction to the integral closed fibre is nonzero is
relative effective Cartier over a valuation base (Stacks, Tags 0EX8 and 062Y).
Module pullback is `tensorPullback` (def-pc-module-pullback); the restriction of `s` to the
fibre `X₀ = f.fiber x₀` is the unit of its canonical adjunction
(lem-pc-module-pullback-adjunction) applied to `s`.

Proof: `Z(s)` is locally principal (lem-pc-zero-scheme-properties (1)): on an affine open
`Spec B` where `M` is free on `e` and `s = a e`, `Z(s) ∩ U = Spec (B/(a))`, so its closed fibre
is `Z(s|_{X₀})`. As `s|_{X₀}` is a nonzero section of an invertible module on the integral
scheme `X₀`, `Z(s|_{X₀})` is an effective Cartier divisor (lem-pc-nonzero-section-integral-cartier).
For `x ∈ Z(s)` the closure `C` of `x` lies in `Z(s)`, `f(C)` is closed and nonempty
(lem-weil-pbc-proper-closed-image), hence contains the closed point of the local scheme
`Spec A`; so `x` specializes to some `y ∈ Z(s)` in the closed fibre. The local fibre-Cartier
criterion (lem-pc-recd-fibre-cartier-local; `f` flat, locally of finite presentation) gives an
open `U_y ∋ y`, hence `∋ x`, on which `Z(s)` is relative effective Cartier. These opens with
`X \ Z(s)` cover `X`, and the property is local, so `Z(s)` is a relative effective Cartier
divisor; in particular `Z(s) → Spec A` is flat (def-pc-relative-effective-cartier).
(blueprint: lem-sc-valuation-zero-section-relative-cartier) -/
theorem valuation_zero_section_relative_cartier
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (x₀ : Spec (.of A)) (hx₀ : IsClosed ({x₀} : Set (Spec (.of A))))
    [IsIntegral (f.fiber x₀)]
    (M : X.Modules) [M.IsInvertible] (s : Γ(M, ⊤))
    (hs₀ : ((Classical.choose (exists_tensorPullbackAdjunction (f.fiberι x₀))).unit.app M).val.app
      (op ⊤) s ≠ 0) :
    Scheme.IdealSheafData.IsRelativeEffectiveCartier
      (Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection M s)) f := by
  sorry

end Modules
end Scheme
end AlgebraicGeometry
