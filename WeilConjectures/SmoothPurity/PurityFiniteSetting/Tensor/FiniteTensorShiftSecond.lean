/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # One-variable shift compatibility of the normalized finite tensor comparison

Source: Stacks 07A4 and 0FNH, parent proof Step 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The normalized finite tensor comparison respects a shift in its second input.
Source: Stacks 07A4 and 0FNH, parent proof Step 6.
(blueprint: lem-pur-finite-tensor-shift-second).
Proof: Choose flat-term K-flat representatives for both inputs and extend scalars
termwise. Change of rings preserves their flatness and K-flatness without requiring
the coefficient quotient to be flat. On a summand with first degree p,
the second-variable shift contributes (-1)^(np).
The scalar-first tensor comparison preserves the degree and the ring map preserves
minus one, so the cochain tensor-comparison shift square commutes. Descend this
square through K-flat localization. The representative-normalized scalar shift
agrees with the shift from the exact restriction adjunction by the counit shift
uniqueness theorem. The normalized tensorator agrees with the descended binary
comparison by existsUnique_finiteTensorCore. The native derived tensor shift is
normalized by the same cochain comparison. Naturality along the representative
isomorphisms gives the displayed equality for arbitrary derived inputs, for every
integer n, including zero and negative n. -/
theorem finiteTensorShiftSecond (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u})
    (U V : _root_.DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) (n : ℤ) :
    (P.finiteTensorReduction m hm hmn T).map
        ((((curriedTensor _).obj U).commShiftIso n).hom.app V) ≫
      (P.finiteTensorScalarShift m hm hmn T n).hom.app (U ⊗ V) ≫
      ((P.finiteTensorCore m hm hmn T).μIso U V).inv⟦n⟧' =
    ((P.finiteTensorCore m hm hmn T).μIso U (V⟦n⟧)).inv ≫
      (P.finiteTensorReduction m hm hmn T).obj U ◁
        ((P.finiteTensorScalarShift m hm hmn T n).hom.app V) ≫
      ((((curriedTensor _).obj ((P.finiteTensorReduction m hm hmn T).obj U)).commShiftIso n).hom.app
        ((P.finiteTensorReduction m hm hmn T).obj V)) := by sorry

end WeilConjectures.PurityFiniteSetting
