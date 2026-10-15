module
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The divisor quotient of the canonical strict henselization is a domain.
Source: Stacks Project, Tag 00NP.
Proof: The local-structure theorem makes the canonical strict henselization local.
Since b(f) is not a unit, its principal ideal is proper, so the quotient is nontrivial
and local. The regularity component makes this quotient regular, hence regular local.
Apply the proved upstream theorem that a regular local ring is a domain.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-domain-part)
-/
theorem strictHenselizationRing_divisor_quotient_domain_part
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  obtain ⟨hlocal, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure barY
  let := hlocal
  let := strictHenselizationRing_regular_divisor_quotient_part R f barY b hb hg
  have hproper : Ideal.span {b.hom f} ≠ ⊤ := fun h ↦
    hg (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let := IsRegularLocalRing.of_isRegularRing_of_isLocalRing
    (R := strictHenselizationRing barY ⧸ Ideal.span {b.hom f})
  infer_instance

end AlgebraicGeometry.Scheme
