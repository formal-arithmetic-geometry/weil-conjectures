/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Independence of Koszul regularity from a smooth ambient scheme

Source: Stacks Project, More on Morphisms, Tag 069E
(blueprint: lem-sfb-koszul-immersion-smooth-ambient-independence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Koszul regularity near a source point is independent of the smooth ambient
scheme over a common base. The equality of composites expresses that the two
immersions are over the same base. Finite equation lengths may vary and may be zero.

Source: Stacks Project, More on Morphisms, Tag 069E, using Divisors, Tags 067S and 0693
(blueprint: lem-sfb-koszul-immersion-smooth-ambient-independence).

Proof plan:
1. Fix `t` and an open source neighbourhood `V` on which `i` is Koszul-regular.
   Restrict both immersions to `V`. To see these remain immersions, factor each
   through a closed immersion into an open target and remove the image of the
   closed complement of `V` from that target.
2. Form `Q = P ×_S P'` (def-pc-fibre-product). Both projections are smooth:
   local finite presentation survives base change by clause (3) of
   lem-weil-pbc-qcqs-morphism-permanence; the formal smoothness lifting property
   in def-sbc-smooth-morphisms lifts the other component of a map from an affine
   first-order thickening, and the product universal property supplies the lift.
3. The product map `j = (i|V, i'|V)` is an immersion because its composite with
   the first projection is one (lem-zl-immersion-cancellation).
4. Apply lem-sfb-koszul-immersion-smooth-lift (Tag 067S) to `j` and the first
   projection: that projection is smooth, both source maps are immersions, and
   their composite `i|V` is Koszul-regular. Thus `j` is Koszul-regular.
5. Apply lem-sfb-koszul-immersion-smooth-push (Tag 0693) to `j` and the second
   projection to conclude that `i'|V` is Koszul-regular. Interchange the two
   ambient schemes and repeat to obtain the converse. No separation, flatness,
   quasi-compactness or Noetherian hypothesis is used. -/
theorem isKoszulRegularImmersionNear_smoothAmbient_iff
    {S T P P' : Scheme.{u}} (p : P ⟶ S) (p' : P' ⟶ S)
    (i : T ⟶ P) (i' : T ⟶ P') [Smooth p] [Smooth p']
    [IsImmersion i] [IsImmersion i'] (h : i ≫ p = i' ≫ p') (t : T) :
    IsKoszulRegularImmersionNear i t ↔ IsKoszulRegularImmersionNear i' t := by
  sorry

end AlgebraicGeometry
