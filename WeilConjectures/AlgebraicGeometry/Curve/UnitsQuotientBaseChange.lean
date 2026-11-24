/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.GroupTheory.QuotientGroup.Defs
import WeilConjectures.AlgebraicGeometry.AffineUnitDivisorBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers

/-!
# Units modulo powers under algebraically closed base change
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem quotient_powers_equiv
    {A B D E : Type*} [CommGroup A] [CommGroup B] [CommGroup D] [CommGroup E]
    (p : A →* B) (d : A →* D) (d' : B →* E) (i : D ≃* E) (n : ℕ)
    (hcomm : ∀ a, d' (p a) = i (d a))
    (hrange : i '' Set.range d = Set.range d')
    (hk : ∀ a, d a = 1 → ∃ b, b ^ n = a)
    (hk' : ∀ a, d' a = 1 → ∃ b, b ^ n = a) :
    ∃ e : (A ⧸ (powMonoidHom n : A →* A).range) ≃*
        (B ⧸ (powMonoidHom n : B →* B).range),
      ∀ a, e (QuotientGroup.mk a) = QuotientGroup.mk (p a) := by
  let N := (powMonoidHom n : A →* A).range
  let M := (powMonoidHom n : B →* B).range
  have hp : N ≤ M.comap p := by
    rintro _ ⟨a, rfl⟩
    exact ⟨p a, (map_pow p a n).symm⟩
  let q := QuotientGroup.map N M p hp
  have hinj : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have hpa : p a ∈ M := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨b, hb⟩ := hpa
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hrange.symm ▸ (Set.mem_range_self b : d' b ∈ Set.range d')
    have hdc : d (a / c ^ n) = 1 := by
      apply i.injective
      rw [map_one, map_div d, map_pow d, map_div i, map_pow i, ← hcomm, hc,
        ← map_pow d']
      change d' (p a) / d' (b ^ n) = 1
      rw [show b ^ n = p a from hb, div_self']
    obtain ⟨z, hz⟩ := hk _ hdc
    have ha : a ∈ N := by
      refine ⟨z * c, ?_⟩
      change (z * c) ^ n = a
      rw [mul_pow, hz, div_mul_cancel]
    exact (QuotientGroup.eq_one_iff a).mpr ha
  have hsurj : Function.Surjective q := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hrange.symm ▸ (Set.mem_range_self b : d' b ∈ Set.range d')
    have hd : d' (b / p a) = 1 := by
      rw [map_div, hcomm, ha, div_self']
    obtain ⟨z, hz⟩ := hk' _ hd
    refine ⟨QuotientGroup.mk a, ?_⟩
    change QuotientGroup.mk (p a) = QuotientGroup.mk b
    apply (QuotientGroup.eq_iff_div_mem).mpr
    refine ⟨z⁻¹, ?_⟩
    change (z⁻¹) ^ n = p a / b
    rw [inv_pow, hz, inv_div]
  exact ⟨MulEquiv.ofBijective q ⟨hinj, hsurj⟩, fun _ ↦ rfl⟩

/-- Pullback identifies units modulo `n`-th powers after extending algebraically closed fields.
The equation on representatives specifies that the isomorphism is induced by pullback. -/
theorem units_quotient_base_change
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (Γ(C, ⊤)ˣ ⧸ (powMonoidHom n : Γ(C, ⊤)ˣ →* Γ(C, ⊤)ˣ).range) ≃*
        (Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ ⧸
          (powMonoidHom n :
            Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ →*
            Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ).range),
      ∀ a : Γ(C, ⊤)ˣ,
        e (QuotientGroup.mk a) =
          QuotientGroup.mk (Units.map (pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom a) := by
  classical
  obtain ⟨c, hc, hs, -, -⟩ := IsConnectedCurve.exists_smooth_properCompactification f
  let : IsConnectedCurve c.g := hc
  let : Smooth c.g := hs
  let t := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let C' := pullback f t
  let f' := pullback.snd f t
  let c' := c.baseChange t
  have hC' := baseChange_curve (k' := k') f
  have hZ' := baseChange_curve (k' := k') c.g
  let : IsConnectedCurve f' := hC'.2.2.2.2.2 inferInstance
  let : Smooth f' := hC'.2.2.1 inferInstance
  let : IsConnectedCurve c'.g := hZ'.2.2.2.2.2 inferInstance
  let : Smooth c'.g := hZ'.2.2.1 inferInstance
  obtain ⟨hI, hN, hI', hN', φ, φ', hφ, hφ', e, -, hcomm, hrange⟩ :=
    affine_unit_divisor_base_change k k' C f c
  let : IsIntegral c.Z := hI
  let : IsNoetherian c.Z := hN
  let : IsIntegral c'.Z := hI'
  let : IsNoetherian c'.Z := hN'
  let d := ((Finsupp.subtypeDomainAddMonoidHom
    (p := fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)).comp
    (c.Z.div.comp (Units.map φ.toMonoidHom).toAdditive)).toMultiplicativeRight
  let d' := ((Finsupp.subtypeDomainAddMonoidHom
    (p := fun P : closedPoints c'.Z ↦ P.val ∉ Set.range c'.i.base)).comp
    (c'.Z.div.comp (Units.map φ'.toMonoidHom).toAdditive)).toMultiplicativeRight
  let i := (Finsupp.domCongr (M := ℤ) e).toMultiplicative
  let p := Units.map (pullback.fst f t).appTop.hom.toMonoidHom
  apply quotient_powers_equiv p d d' i n
  · exact hcomm
  · exact hrange
  · intro a ha
    exact boundary_divisor_kernel_powers k C f c φ hφ n hn a ha
  · intro a ha
    exact boundary_divisor_kernel_powers k' C' f' c' φ' hφ' n hn a ha

end AlgebraicGeometry
