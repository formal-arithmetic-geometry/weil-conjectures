/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionExistence

/-! # Repetition and compact-support data for a cofinal tower

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
(blueprint: lem-pur-etale-cofinal-repeat-support-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The geometric repetition/support package exists for every coefficient tower.
Source: Zheng, Construction 4.1, printed pp. 21--23.

Proof: choose the ordinary projection presentation from
`etaleSystemProjectionTheory_nonempty`. Let `t(m)` be the least selected index
with `m ≤ r(t(m))`. Its finite nonempty fibers give the endpoint and repetition
data of `systemBlockRepetition` on each of the three étale sequence sites.
The geometric block square and the section-normalized open-extension square,
followed by the universal derived comparison, supply the proper, openImage and
K-injective fields of `CofinalRepeatSupport`.
(blueprint: lem-pur-etale-cofinal-repeat-support-existence) -/
theorem etaleCofinalRepeatSupport_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (T : Theory c l) (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :
    Nonempty (CofinalRepeatSupport T B r) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
