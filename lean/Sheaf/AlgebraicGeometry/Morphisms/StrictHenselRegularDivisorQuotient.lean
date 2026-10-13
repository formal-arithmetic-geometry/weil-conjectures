/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # The regular divisor quotient of the canonical strict henselization
Source: Stacks Project, Tag 0EYG, strict henselization paragraph; Tags 06LN and 05WS.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The canonical strict henselization is Noetherian and its nonempty divisor quotient
is a regular domain.
Source: Stacks Project, Tag 0EYG, strict henselization paragraph, using quotient
compatibility (Tag 05WS) and regularity of strict henselizations (Tag 06LN).
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient)

Proof: Let y be the image of the unique point of Spec Omega. The affine pointed
neighbourhood colimit identifies with the strict henselization of R localized at y.
That local ring is Noetherian and regular because R is regular. Strict henselization
preserves Noetherianness. The identity on Spec forces b to be its canonical map.
The nonunit condition says y is on the divisor. Quotient compatibility identifies
H/(b(f)) with the strict henselization of (R/(f)) localized at y. This is regular
local since R/(f) is regular. A regular local ring is a domain, and all its prime
localizations are regular local, so it is a regular ring. The nonunit condition
excludes the zero quotient; no choice of an arbitrary ring witness is made. -/
theorem strictHenselization_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY) ∧
      IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  sorry

end AlgebraicGeometry.Scheme
