/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicProjectionShiftData
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # AdicExceptionalShiftCoherence

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, adic Step 2
(blueprint: lem-pur-adic-exceptional-transpose-shift). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open IntegralSystemRealization

section Exceptional
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (F : Type u) [Field F] [Algebra ℚ_[C.l] F] [FiniteDimensional ℚ_[C.l] F]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : ConstructibleExceptionalCoefficients.RingSystem C.l C.Qbar D C.different (f := f))
  (c : Compactification f)

/-- Transposition through the specified realized exceptional adjunction preserves
any ambient shift square. The source comparison and both maps are arbitrary.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-exceptional-transpose-shift).

Proof: lift a into the full finite-Tor subcategory by composing it with the
inverse inclusion shift comparison. The ofComp construction of adicSupportShift
makes S.left commute with the composite shift. Naturality of S.left therefore
turns the given ambient square into the corresponding square between its
left-adjoint images. Write the Hom transpose as eta followed by G(v).
Naturality of eta moves the lifted source arrow to the left; naturality of
the right shift moves G(v[1]) past its shift comparison. The unit shift
equation cancels the remaining shift comparisons, giving the transposed
square in the full subcategory. Apply the fully faithful ambient inclusion,
use its shift naturality and cancel the inverse source inclusion comparison.
This uses no projection invertibility and no particular construction of v. -/
theorem adicExceptionalTransposeShift
    (A₀ A₁ : finiteTorConstructibleIntegralCategory C.l F X)
    (K : finiteTorConstructibleIntegralCategory C.l F Y)
    (a : A₁.obj ⟶ A₀.obj⟦(1 : ℤ)⟧)
    (v₀ : (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj A₀.obj ⟶ K.obj)
    (v₁ : (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj A₁.obj ⟶
      (K⟦(1 : ℤ)⟧).obj)
    (hv : v₁ ≫ (adicInputShift C.l F Y K).hom =
      (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).map a ≫
        ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).commShiftIso
          (1 : ℤ)).hom.app A₀.obj ≫ v₀⟦(1 : ℤ)⟧') :
    adicTranspose D C F f S c A₁ (K⟦(1 : ℤ)⟧) v₁ ≫
        ((adicExceptionalShift D C F f S c).hom.app K).hom ≫
        (adicInputShift C.l F X
          ((S.operation c (.integral { carrier := F })).G.obj K)).hom =
      a ≫ (adicTranspose D C F f S c A₀ K v₀)⟦(1 : ℤ)⟧' := by sorry

end Exceptional
end WeilConjectures
