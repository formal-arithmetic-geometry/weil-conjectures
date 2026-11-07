/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
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
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsRegularRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselization barY ⧸ Ideal.span {b.hom f}) := by
  exact ⟨strictHenselizationRing_regular_divisor_quotient_part R f barY b hb hg,
    strictHenselizationRing_divisor_quotient_domain_part R f barY b hb hg⟩
end AlgebraicGeometry.Scheme
