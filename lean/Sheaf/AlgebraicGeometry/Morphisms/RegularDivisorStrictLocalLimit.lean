/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Strict local limits of regular divisors

Source: Stacks Project, Tag 0EYG, strict henselization paragraph; Tags 04GP, 04HX, 06LN and 05WS.
(blueprint: lem-sbc-regular-divisor-strict-local-limit)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A regular divisor has a pointed regular strict local ind-etale limit.

Source: Stacks Project, Tag 0EYG, strict henselization paragraph; Tags 04GP,
04HX, 06LN and 05WS for strict henselization and passage to the quotient.
(blueprint: lem-sbc-regular-divisor-strict-local-limit)

Proof: Localize R at y, choose a separable closure of its residue field, and
form its strict henselization H as the filtered colimit of pointed etale
neighbourhood algebras. Its structural map from R is ind-etale (localization
is ind-etale, and so is this filtered etale colimit). H is strictly henselian
local, and the contraction of its maximal ideal is y; take x to be its
closed point. The local ring of R at y is regular, so H is regular local
by Tag 06LN. Flatness of R to H preserves injective multiplication by g.
Because g belongs to y, its image lies in the maximal ideal of H. The
quotient H/(g) is the strict henselization of the localization of R/(g)
at the image of y (Tag 05WS); it is regular local by Tag 06LN. These
constructions all stay in the universe of R using small representatives.
Edge cases: y excludes the zero ring, and hy excludes a unit g. A regular
g=0 can occur only in the zero ring, so cannot satisfy these hypotheses. -/
theorem regular_divisor_strict_local_limit
    (R : CommRingCat.{u}) (g : R) [IsRegularRing R]
    (hg : IsSMulRegular R g) [IsRegularRing (R ⧸ Ideal.span {g})]
    (y : Spec R) (hy : g ∈ y.asIdeal) :
    ∃ (H : CommRingCat.{u}) (ι : R →+* H),
      ι.IndEtale ∧
      ∃ (hH : IsStrictlyHenselianLocalRing H),
        IsRegularLocalRing H ∧ IsRegularLocalRing (H ⧸ Ideal.span {ι g}) ∧
        IsSMulRegular H (ι g) ∧
        ι g ∈ IsLocalRing.maximalIdeal H ∧
        ∃ x : Spec H, (Spec.map (CommRingCat.ofHom ι)) x = y := by sorry

end AlgebraicGeometry.Scheme
