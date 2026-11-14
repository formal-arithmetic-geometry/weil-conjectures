/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.RegularLocalLocalization

/-! Local regularity and Noetherianity of the strict henselization divisor quotient. -/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The divisor quotient has the local regularity properties needed to assemble a regular ring.
Source: Stacks Project, Tags 05WS and 06LN.
The presentation theorem identifies the quotient as an algebraic strict henselization of
a prime localization of `R/(f)`, without using regularity. The localization is regular
local by the assumed regularity of `R/(f)`. Apply the strict-henselization regularity
equivalence to deduce regular locality of the quotient, hence its Noetherianity. Finally
apply regular-local localization at every prime of the quotient.
-/
theorem strictHenselizationRing_divisor_quotient_noetherian_and_local_regular
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) ∧
      ∀ (p : Ideal (strictHenselization barY ⧸ Ideal.span {b.hom f}))
        [p.IsPrime],
    IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨p, hp, K, hK, aK, hsep, aLK, hLK, aLH, hH⟩ :=
    strictHenselizationRing_divisor_quotient_presentation R f barY b hb hg
  let := hp
  let := hK
  let := aK
  let := hsep
  let := aLK
  let := hLK
  let := aLH
  have hregL : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  have hregH : IsRegularLocalRing
      (strictHenselization barY ⧸ Ideal.span {b.hom f}) :=
    (Algebra.isRegularLocalRing_iff_strictHenselization
      (Localization.AtPrime p) K _ hH).mp hregL
  let := hregH
  refine ⟨inferInstance, fun q hq ↦ ?_⟩
  exact (IsRegularLocalRing.localization_at_prime_and_isRegularRing q).1

end AlgebraicGeometry.Scheme
