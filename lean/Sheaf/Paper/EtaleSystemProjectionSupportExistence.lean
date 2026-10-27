/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleSystemProjectionData

/-! # Support operations for normalized etale systems

Source: Zheng, Constructions 4.1 and 5.14--5.15; Stacks Tag 0GL6
(blueprint: lem-pur-etale-system-projection-support-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The proper/open support presentations exist for every finite coefficient sequence.
Source: Zheng Constructions 4.1 and 5.14--5.15; Stacks 03D2, 03S2, 07A4
(blueprint: lem-pur-etale-system-projection-support-existence).

Proof: On each vertical sequence site, use the normalized structural map on constant
coefficient generators to form the module-sheaf proper direct image. Its exact inverse
image is obtained from the sheaf-ring coefficient adjunction. For the open factor,
localization of the etale site gives the exact extension-by-zero left adjoint. The
proper and open choices together form `Support`; the K-injective and derived
interfaces are the fields inherited from the fixed ordinary constructions.
-/
theorem etaleSystemProjectionSupportData_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) :
    Nonempty (∀ B : Coefficients.{u} l, Support c B.rings) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
