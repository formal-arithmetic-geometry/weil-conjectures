/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Compactification.Defs
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import Sheaf.AlgebraicGeometry.HenselianClopenRestriction

/-!
# Lifting a proper clopen part over a henselian pair

Source: Stacks Project, More on Morphisms, Tag 0CT9,
`lemma-split-off-proper-part-henselian`
(blueprint: lem-per-henselian-pair-proper-clopen-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper clopen subscheme of the closed fibre lifts to a proper clopen subscheme
of a separated finite type scheme over a henselian pair.
Source: Stacks Project, Tag 0CT9, `lemma-split-off-proper-part-henselian`
(blueprint: lem-per-henselian-pair-proper-clopen-lift).

The opens `Y` and `W` carry their restricted scheme structures. The last equality is
equality of opens in the closed fibre, and hence of its open subschemes, including
their structure sheaves: base change of an open subscheme is its inverse-image open
(`pullbackRestrictIsoRestrict`). No local or Noetherian hypothesis is imposed on `A`.

Proof:
1. The affine base is quasi-compact and quasi-separated
   (`lem-weil-pbc-qcqs-over-affine`). Apply `thm-nagata-compactification` and unpack
   `def-nagata-compactification` and `def-nagata-compactifiable` to obtain an open
   immersion into a proper scheme over the base.
2. Base change the open immersion (`lem-weil-pbc-open-immersion-base-change`). The
   image of `Y` is open in the compactification's closed fibre. That fibre is proper,
   hence separated (`lem-weil-pbc-proper-fp-permanence`, `def-weil-proper-morphism`),
   so the map from the proper `Y` is proper (`lem-weil-pbc-proper-over-separated`).
   Its image is therefore closed as well.
3. Apply `lem-weil-pbc-henselian-clopen-restriction` on the proper compactification
   to lift this clopen to a clopen open subscheme. A clopen inclusion is a closed
   immersion, so the lift is proper (`lem-weil-pbc-closed-immersion-proper`). Its
   closed fibre is the prescribed open subscheme by open-immersion base change.
4. The boundary outside the original scheme is closed in this proper lift and
   misses its closed fibre. If nonempty, the closure of one of its points would
   contradict the nonempty fibre-intersection clause of
   `lemma-weil-pbc-stein-connectedness`. Thus the boundary is empty.
5. Restrict the lifted clopen along the original open immersion
   (`def-weil-open-immersion`). Its restriction is isomorphic to the lift, hence
   proper, and its closed fibre is exactly `Y` as an open subscheme, by
   `lem-weil-pbc-open-immersion-base-change`. -/
theorem Scheme.exists_proper_clopen_lift_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Y : (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Opens)
    (hY : IsClosed (Y : Set (pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})))
    [IsProper (Y.ι ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ W : X.Opens, IsClosed (W : Set X) ∧ IsProper (W.ι ≫ f) ∧
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⁻¹ᵁ W = Y := by
  sorry

end AlgebraicGeometry
