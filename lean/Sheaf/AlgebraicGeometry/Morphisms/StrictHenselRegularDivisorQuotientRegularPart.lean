module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! Regularity component of the canonical strict henselization divisor quotient. -/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The quotient by the divisor remains regular after passage to the canonical strict henselization.
Source: Stacks Project, Tags 05WS and 06LN.
Proof: Let p be the image of the geometric point. Identify the pointed-neighbourhood
colimit with the strict henselization of R localized at p, compatibly with the structural
map b (by hb and full faithfulness of Spec). This is a local map, so hg implies f belongs
to p. Localization commutes with quotient, and the localization of R/(f) at p/(f) is
regular local by the assumed regularity of R/(f). Tag 05WS identifies its strict
henselization with the quotient by b(f); Tag 06LN preserves its regularity. A regular
local ring is a regular ring, giving the conclusion.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-regular-part)
-/
theorem strictHenselizationRing_regular_divisor_quotient_part
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  sorry

end AlgebraicGeometry.Scheme
