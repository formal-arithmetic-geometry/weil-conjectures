/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.LocalProperties.Submodule

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Exactness of the Cech sequence for a module localization cover

Source: Stacks Project, Algebra, Lemma 00EK (label `lemma-cover-module`)
(blueprint: lem-weil-pbc-cover-module-exact).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- Powers of a divisor of `h` act invertibly on `M_h`. This is the invertibility
needed in the notation step of Stacks Project, Algebra, Lemma 00EK, using the universal
property in Lemma 07K0 (blueprint: lem-weil-pbc-cover-module-exact).

Proof: write `h = a * b`. Multiplication by `h` is a unit endomorphism of `M_h`, by
`IsLocalizedModule.map_units`. The commuting endomorphisms given by `a` and `b` therefore
are units individually. Every element of `Submonoid.powers a` is a power of `a`, so its
endomorphism is a unit as well. No map or localization is defined anew here. -/
theorem localizationAway_map_units_of_dvd {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (a h : R) (ha : a ∣ h) :
    ∀ x : Submonoid.powers a,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away h M)) (x : R)) := by
  obtain ⟨b, rfl⟩ := ha
  have hh := IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
    (⟨a * b, Submonoid.mem_powers _⟩ : Submonoid.powers (a * b))
  rw [map_mul] at hh
  have hab : Commute
      (algebraMap R (Module.End R (LocalizedModule.Away (a * b) M)) a)
      (algebraMap R (Module.End R (LocalizedModule.Away (a * b) M)) b) :=
    (Commute.all a b).map _
  have hu := (hab.isUnit_mul_iff.mp hh).1
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := hx
  simpa only [map_pow] using hu.pow k


end RingTheory
