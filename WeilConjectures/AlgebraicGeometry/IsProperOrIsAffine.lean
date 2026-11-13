/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Curve.Compactification

@[expose] public section

/-!
# A smooth separated connected curve is proper or affine

## References

* Stacks Project, Varieties, Lemma 33.43.11 (Tag 0A28).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- Reference: Stacks, Tag 0A28. -/
set_option linter.style.haveILetI false in
/-- A smooth separated connected curve over an algebraically closed field is proper or affine. -/
theorem IsConnectedCurve.isProper_or_isAffine
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] :
    IsProper f ∨ IsAffine C := by
  obtain ⟨c, hc, hs, hfin, hclosed⟩ :=
    IsConnectedCurve.exists_smooth_properCompactification f
  by_cases hS : (Set.range c.i.base)ᶜ = ∅
  · left
    have hrange : Set.range c.i.base = Set.univ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        by_contra hxn
        have hxc : x ∈ (Set.range c.i.base)ᶜ := by
          simpa [Set.mem_compl_iff] using hxn
        rw [hS] at hxc
        exact hxc
    have hsurj : Function.Surjective c.i.base := Set.range_eq_univ.mp hrange
    letI : Surjective c.i := ⟨hsurj⟩
    haveI : IsIso c.i := (isIso_iff_isOpenImmersion_and_surjective c.i).mpr
      ⟨inferInstance, inferInstance⟩
    rw [c.comm]
    infer_instance
  · right
    let V : c.Z.Opens := c.i.opensRange
    have hV : V ≠ ⊤ := by
      intro h
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS
      have hx' : x ∈ (V : Set c.Z) := by
        rw [h]
        trivial
      exact hx hx' 
    have hAff : IsAffine V :=
      IsConnectedCurve.isAffine_of_ne_top c.g V hV
    exact IsAffine.of_isIso c.i.isoOpensRange.hom

end AlgebraicGeometry
