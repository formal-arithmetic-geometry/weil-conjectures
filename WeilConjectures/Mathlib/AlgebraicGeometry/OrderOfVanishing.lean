/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing of elements of local rings

- `AlgebraicGeometry.Scheme.ord_algebraMap_stalk`: the order of vanishing of an element of a local
  ring is its ring-theoretic order.
-/

@[expose] public section

open Order

namespace AlgebraicGeometry

/-- On a locally noetherian integral scheme, the order of vanishing at a point of codimension
one of an element of the local ring is its ring-theoretic order `ord_{𝒪_x}(s)`. -/
theorem Scheme.ord_algebraMap_stalk {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {x : X}
    (hx : coheight x = 1) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {s : X.presheaf.stalk x} (hs : s ≠ 0) :
    X.ord (algebraMap _ X.functionField s) x = (Ring.ord (X.presheaf.stalk x) s).toNat := by
  have hs' : algebraMap _ X.functionField s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs
  rw [Scheme.ord_eq_iff hx hs']
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  change Ring.ordFrac (X.presheaf.stalk x) _ = _
  rw [Ring.ordFrac_eq_ord _ hs]
  have hmem : s ∈ nonZeroDivisors (X.presheaf.stalk x) := mem_nonZeroDivisors_of_ne_zero hs
  have hfin : Ring.ord (X.presheaf.stalk x) s ≠ ⊤ := Ring.ord_ne_top hmem
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only [Ring.ordMonoidWithZeroHom, hmem, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    if_true, ← hn, ENat.recTopCoe_natCast, ENat.toNat_natCast]

end AlgebraicGeometry
