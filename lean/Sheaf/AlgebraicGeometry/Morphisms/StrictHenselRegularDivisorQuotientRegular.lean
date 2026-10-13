module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationLocalStructure
public import Mathlib.RingTheory.RegularLocalRing.Defs
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Regularity and integrality of the divisor quotient in the canonical strict henselization.
Source: Stacks Project, Tags 05WS and 06LN, using the local structure at the geometric point.
The quotient is identified with the strict henselization of the regular local divisor ring.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-regular)
-/
theorem strictHenselizationRing_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  sorry
end AlgebraicGeometry.Scheme
