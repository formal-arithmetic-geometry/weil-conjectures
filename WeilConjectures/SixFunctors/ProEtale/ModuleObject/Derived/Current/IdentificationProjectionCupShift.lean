/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaShift

/-! # The native exceptional projection commutes with shifts

Source: the first paragraph of the proof of sk-thm-sf-identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.Current

/-- The compactification exceptional projection commutes with every integer shift in
its second variable. Source: sk-thm-sf-identification, proof first paragraph, and the
native proved projection-formula shift instance.

Proof: for a compactification, the proper projection is the mate of the shifted
pullback tensor comparison. The open projection is the analogous extension-by-zero
mate; its inverse commutes with shifts as well. Whisker and compose these maps with
the compactification pullback comparison. The native instance proves precisely this
compatibility for the defined exceptional projection. Apply that instance. No
boundedness, nonzero-object or nonempty-scheme hypothesis is used.
(blueprint: lem-sf-identification-projection-cup-shift). -/
theorem identification_exceptionalProjection_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (cf : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    NatTrans.CommShift
      (exceptionalProjectionMorphismOfCompactificationNatTrans Λ cf K) ℤ := by
  exact commShift_exceptionalProjectionMorphismOfCompactificationNatTrans Λ cf K

end AlgebraicGeometry.ProEtale.CondensedRing.Current
