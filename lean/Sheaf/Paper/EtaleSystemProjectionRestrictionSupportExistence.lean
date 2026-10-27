/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleSystemProjectionBasicData

/-! # Restriction support comparison existence for normalized etale systems

Source: Zheng, Construction 4.1, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The normalized restriction comparison exists for compactly supported systems.
Source: Zheng Lemma 5.16; Stacks 0GL6.
(blueprint: lem-pur-etale-system-projection-restriction-support-existence).

Proof: Restriction of the proper direct image is fixed on sections, and its inverse-image
mate is pasted with the exact open restriction mate. Localizing this ordinary square gives
the prescribed restriction comparison for compact support.
-/
theorem restrictionSupport_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) :
    Nonempty (RestrictionSupport a (b.support B) (b.support C)) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
