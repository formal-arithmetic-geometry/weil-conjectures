/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Shift compatibility of the compact-support restriction square

Source: Stacks Tag 07A6; the restriction square used by the scalar mate
(blueprint: lem-pur-compact-support-restriction-shift).

The proof is split from the ambient coefficient comparison: the restriction
square is built from the exact open restriction comparison and the canonical
proper direct-image restriction comparison. Both pieces commute with integer
shifts by their normalized derived adjunctions; the pasted square therefore
commutes with shifts. This auxiliary statement records exactly that lower step.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

/-- The compact-support restriction square commutes with integer shifts.
STATEMENT-DISPUTED: the four arbitrary `CommShift` instances do not determine
compatible shift structures on the two sides of an arbitrary isomorphism.
For distinct choices of coherent shift structures, an isomorphism need not commute
with both; an additional compatibility hypothesis (or canonical instances) is required.
Source: Stacks Tag 07A6; the normalized open/proper scalar square.
(blueprint: lem-pur-compact-support-restriction-shift).
Proof: the open restriction comparison is the derived map of the exact
open scalar square, and the proper restriction comparison is the canonical
right-derived direct-image comparison. Their shift equations compose, so
`restriction a c` has a shift-compatible hom. -/
theorem restriction_commShift {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [hRX : (pbcDerivedRestrict (a.map X)).CommShift ℤ]
    [hIR : (image R c).CommShift ℤ]
    [hIS : (image S c).CommShift ℤ]
    [hRY : (pbcDerivedRestrict (a.map Y)).CommShift ℤ] :
    NatTrans.CommShift (restriction a c).hom ℤ := by
  sorry

end WeilConjectures.PurCompactSupport
