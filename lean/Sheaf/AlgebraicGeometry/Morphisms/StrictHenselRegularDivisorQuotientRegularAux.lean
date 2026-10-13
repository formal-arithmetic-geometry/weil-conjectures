module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! Local regularity and Noetherianity of the strict henselization divisor quotient. -/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The divisor quotient has the local regularity properties needed to assemble a regular ring.
Source: Stacks Project, Tags 05WS and 06LN.
The quotient is identified with the strict henselization of the localization of `R/(f)`
at the image of the geometric point. Strict henselization preserves Noetherianity and regular
local rings; localizing at every prime then gives the asserted family.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-regular-part-aux)
-/
theorem strictHenselizationRing_divisor_quotient_noetherian_and_local_regular
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      ∀ (p : Ideal (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}))
        [p.IsPrime],
        IsRegularLocalRing (Localization.AtPrime p) := by
  sorry

end AlgebraicGeometry.Scheme
