/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Basic

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


/-- **The order of vanishing is local.** Let `f : X ⟶ Y` be an open immersion of locally
noetherian integral schemes and `φ : k(Y) ⟶ k(X)` a ring map compatible at `x` with the
isomorphism of local rings `𝒪_{Y,f x} ⟶ 𝒪_{X,x}`. Then `ord_x (φ g) = ord_{f x} g`. -/
theorem Scheme.ord_map_of_isOpenImmersion {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
    (φ : Y.functionField →+* X.functionField)
    (hφ : ∀ s, φ (algebraMap (Y.presheaf.stalk (f x)) Y.functionField s) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x s))
    (g : Y.functionField) : X.ord (φ g) x = Y.ord g (f x) := by
  let e := (CategoryTheory.asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  have hcoh : coheight (f x) = coheight x := by
    have h₁ := ringKrullDim_stalk_eq_coheight x
    have h₂ := ringKrullDim_stalk_eq_coheight (f x)
    rw [← ringKrullDim_eq_of_ringEquiv e] at h₁
    exact_mod_cast h₂.symm.trans h₁
  by_cases hx : coheight x = 1
  · have hy : coheight (f x) = 1 := hcoh.trans hx
    by_cases hg : g = 0
    · rw [hg, map_zero, ord_zero, ord_zero]
      rfl
    have hφg : φ g ≠ 0 := (map_ne_zero_iff _ φ.injective).2 hg
    have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk (f x)) := krullDimLE_of_coheight_le hy.le
    have key : X.ordHom x hx (φ g) = Y.ordHom (f x) hy g :=
      Ring.ordFrac_map_of_ringEquiv e φ hφ g
    rw [ord_eq_unzero_ordHom hx hφg, ord_eq_unzero_ordHom hy hg]
    congr 1
    exact WithZero.coe_injective (by simp [key])
  · rw [ord_eq_zero_of_coheight_neq_one hx, ord_eq_zero_of_coheight_neq_one (hcoh ▸ hx)]

end AlgebraicGeometry
