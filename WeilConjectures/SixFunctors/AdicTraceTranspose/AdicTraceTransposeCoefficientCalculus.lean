/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicTraceTranspose.AdicTraceTransposeData

/-! # Coefficient and shift calculus of integral trace transposes

Source: blueprint sk-thm-purity-transport, Steps 2--3
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.AdicTraceTranspose
open ConstructibleExceptionalCoefficients
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (c : Compactification f.hom.left) (d : ℕ)
  (R : RingSystem.{u} C.l C.Qbar D C.different (f := f.hom.left))

/-- The constructed mate has exactly the counit transpose specified in the node.
Source: definition of b and proof Step 1
(blueprint: lem-pur-adic-trace-transpose-coefficient-calculus).
Proof: the mateEquiv component formula is the adjunction transpose of c inverse
followed by the scalar image of the old counit. This is its defining component
formula, without an invertibility hypothesis. -/
theorem exceptional_counit
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) (K : Cat D C Y E) :
    (exceptionalComparison D C f c R h).app K =
      (operation D C f c R F).adjunction.homEquiv _ _
        ((supportIso D C f c R h).inv.app ((operation D C f c R E).G.obj K) ≫
          (scalar D C f R h false).functor.map
            ((operation D C f c R E).adjunction.counit.app K)) := by
  apply ((operation D C f c R F).adjunction.homEquiv _ _).symm.injective
  change _ = ((operation D C f c R F).adjunction.homEquiv _ _).symm
    ((operation D C f c R F).adjunction.homEquiv _ _ _)
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact mateEquiv_counit (operation D C f c R E).adjunction
    (operation D C f c R F).adjunction
    (TwoSquare.mk _ _ _ _ (supportIso D C f c R h).inv) K


end WeilConjectures.AdicTraceTranspose
