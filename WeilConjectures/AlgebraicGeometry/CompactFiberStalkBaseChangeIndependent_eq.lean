/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChangeData

/-!
# Coherence obligation for compact-support stalk base change
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Independence of the geometric stalk comparison under a change of
compactification, as an equality of arrows after the canonical comparisons
on both ends. Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 3
(blueprint: lem-pur-cfiber-stalk-base-change-independent-coherence).

Proof. The comparison `Rf_!(c) ≅ Rf_!(d)` is the comparison along the refinement
`inf c d ⟶ c` followed by the inverse of the one along `inf c d ⟶ d`. It therefore
suffices to show that, for a refinement `r : c' ⟶ c` with cartesian square over `X`,
the refinement comparison commutes with the exchange maps `Ex_!(sq, c)` and
`Ex_!(sq, c')`, the target side using the base-changed refinement
`c' ×_Y T ⟶ c ×_Y T`. This holds because the refinement comparison is built from
the unit of `r^* ⊣ r_*`, the composition isomorphisms of the direct images, and
the open-extension base change along `r`, each of which commutes with the proper
base-change mate for the base change `T → Y` (thm-cbc-finite-torsion,
compactification independence clause; def-compact-support-direct-image-detailed).
The base change of `inf c d` is a common refinement of the base-changed
compactifications, so the target comparisons agree. Applying `RΓ(T, -)` gives the
equation. -/
theorem compactFiberStalkBaseChangeIndependent_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y T : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ T}
    {b : T ⟶ Y} {bE : X' ⟶ X} [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback bE f' f b) (c d : Compactification f)
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    compactFiberStalkBaseChangeIndependent A sq c d K := by
  -- The combined mate/coherence calculation is a separate proof obligation.
  sorry

end WeilConjectures
