/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.AdicMiddleExtensionConstructible
public import Sheaf.Paper.ConstructibleDegreeZeroProperSupport
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Unique continuation of ordinary middle-extension sections

Source: blueprint main-20261015, lem-fd-stalk-at-origin.proof.md, second paragraph,
the lissity argument; Weil II (1.1.1); Bhatt--Scholze 6.8.4 and 6.8.14
(blueprint: lem-a1-middle-extension-section-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- A section of the ordinary image of a lisse sheaf on a smooth geometrically
connected curve is determined by its restriction to any nonempty open. The curve
need not be affine, and the section need not have proper support.
Source: blueprint lem-fd-stalk-at-origin.proof.md, second paragraph, lissity argument;
Weil II (1.1.1); Bhatt--Scholze 6.8.4 and 6.8.14
(blueprint: lem-a1-middle-extension-section-restriction).

Proof: smoothness and geometric connectedness make the geometric curve integral.
The geometric lisse open is dense, so its intersection with the given nonempty
open is nonempty. Restrict a difference of sections first to the lisse open.
Ordinary direct image identifies these sections with sections of the lisse input:
at every coefficient level (j_*F)(C) = F(U). A geometric point in the intersection
has zero fibre of the difference. On connected U the lisse geometric fibre functor
is faithful, so the difference is zero on U and consequently on C. To apply this
to the recorded coefficient category, represent both arrows at a common finite
coefficient field. The degree-zero derived embedding is fully faithful; the
normalized immersion pullback is ordinary restriction. Clear the uniformizer
denominators in the two rational Hom groups and apply the same finite-level
argument to the integral inverse systems. Their transition maps are compatible,
so equality holds in their inverse limits. Inverting the uniformizer and passing
to the directed colimit of finite coefficient fields preserves this equality.
All comparisons are the actual module adjunction and tensor-unit comparisons,
so this restriction is precisely a1ConstructibleSectionRestriction. Rank zero
causes no exception; the nonempty-open hypothesis excludes the empty curve. -/
theorem adicMiddleExtension_section_eq_zero_of_restriction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c : MiddleExtensionCurve D)
    [SmoothOfRelativeDimension 1 c.C.hom] [GeometricallyConnected c.C.hom]
    [IsSeparated ((D.geometricFiber c.C).left ↘ Spec (.of D.k))]
    (F : adicMiddleExtensionLisse l Ω c hl)
    (V : (D.geometricFiber c.C).left.Opens)
    (hV : (V : Set (D.geometricFiber c.C).left).Nonempty) :
    ∀ s : A1ConstructibleSections l D hl Ω (D.geometricFiber c.C).left
      (adicMiddleExtensionObject l Ω c hl F),
      a1ConstructibleSectionRestriction l D hl Ω (D.geometricFiber c.C).left V s = 0 →
        s = 0 := by
  sorry

end WeilConjectures
