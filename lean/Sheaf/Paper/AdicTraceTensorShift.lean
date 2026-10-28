/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Paper.AdicProjectionShiftData

/-! # AdicTraceTensorShift

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, adic Step 2
(blueprint: lem-pur-adic-trace-tensor-shift). -/

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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Tensoring a trace with the second input respects its signed shift, in the
actual completion-unit and unitor coordinates.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-trace-tensor-shift).

Proof: on flat-term K-flat models the second-slot comparison on a summand
of first degree a is multiplication by (-1)^a. The cochain map representing
t sends that summand to the same first degree, so this sign commutes with
t tensor identity. The tensor unit is concentrated in degree zero; hence its
left unitor commutes with the second-slot comparison without an additional
sign. The quotient-unit augmentation has zero cone coordinate and the same
quotient tensor coordinates on both routes. Products preserve the equality,
and the shifted cone comparison has the prescribed diagonal sign. Descend
through the normalized tensor model comparisons, and invert chi on the
stated inputs. Finally use naturality at the inclusion's shift isomorphism.
This argument allows arbitrary degrees of the first object and any map t;
it neither assumes t invertible nor detects maps by finite evaluation. -/
theorem adicTraceTensorShift {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : RingedModels l E) (c : Compactification f)
    (T : Integral l E X)
    (hχ : ∀ K : finiteTorConstructibleIntegralCategory l E Y,
      IsIso (((d.tensor Y).chi l E).app
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K.obj)))
    (t : (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T ⟶
      (calculus l E Y).integralClosed.monoidal.tensorUnit)
    (K : finiteTorConstructibleIntegralCategory l E Y) :
    adicTraceTensor l E d c T (K⟦(1 : ℤ)⟧).obj (hχ (K⟦(1 : ℤ)⟧)) t ≫
        (adicInputShift l E Y K).hom =
      (integralCompletedTensor l E Y).map
          (Prod.mkHom (𝟙 _) (adicInputShift l E Y K).hom) ≫
        ((tensorShifts l E).integralRight Y 1).hom.app
          ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K.obj) ≫
        (adicTraceTensor l E d c T K.obj (hχ K) t)⟦(1 : ℤ)⟧' := by sorry

end WeilConjectures
