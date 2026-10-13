/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization

@[expose] public section

universe u v
namespace RingTheory

/-- Transport a localized derivation across an isomorphism of away localizations.
Source: Stacks Project, More on Algebra, Tag 07PE, part (2) and the final statement.
(blueprint: lem-weil-pbc-derivation-away-transport)

Proof: apply `Derivation.exists_completion_and_unique_localization` to the powers of `g`,
obtaining `Dw` on `R_g` with `Dw(r/1) = D(r)/1`. Let `e : R_g ≃+* R'_g` be the ring
isomorphism associated to the bijective canonical map. The additive map `e ∘ Dw ∘ e⁻¹`
is integer-linear, sends one to zero, and satisfies Leibniz because `e` and its inverse
preserve addition and multiplication. The localization map commutes with the images of
`R`, so this conjugated derivation sends the image of every `r` to the image of `D(r)`.
-/
theorem exists_derivation_away_transport
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [Algebra R R']
    (_hinj : Function.Injective (algebraMap R R')) (g : R)
    (hiso : Function.Bijective
      (IsLocalization.Away.map (Localization.Away g)
        (Localization.Away (algebraMap R R' g)) (algebraMap R R') g))
    (D : Derivation ℤ R R) :
    ∃ δ : Derivation ℤ (Localization.Away (algebraMap R R' g))
        (Localization.Away (algebraMap R R' g)),
      ∀ r : R, δ (algebraMap R' (Localization.Away (algebraMap R R' g))
        (algebraMap R R' r)) =
        algebraMap R' (Localization.Away (algebraMap R R' g))
          (algebraMap R R' (D r)) := by
  classical
  obtain ⟨Dw, hext, _, _⟩ :=
    (Derivation.exists_completion_and_unique_localization R D).2 (Submonoid.powers g)
  let e := RingEquiv.ofBijective
    (IsLocalization.Away.map (Localization.Away g)
      (Localization.Away (algebraMap R R' g)) (algebraMap R R') g) hiso
  let f : Localization.Away (algebraMap R R' g) →+
      Localization.Away (algebraMap R R' g) :=
    e.toAddMonoidHom.comp (Dw.toLinearMap.toAddMonoidHom.comp e.symm.toAddMonoidHom)
  let δ : Derivation ℤ (Localization.Away (algebraMap R R' g))
      (Localization.Away (algebraMap R R' g)) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro n x
        rw [Algebra.smul_def]
        simpa using f.map_zsmul n x
      map_one_eq_zero' := by simp [f]
      leibniz' := by
        intro x y
        simp [f, Dw.leibniz, smul_eq_mul] }
  have he (r : R) : e (algebraMap R (Localization.Away g) r) =
      algebraMap R' (Localization.Away (algebraMap R R' g)) (algebraMap R R' r) := by
    dsimp [e, IsLocalization.Away.map]
    rw [IsLocalization.map_eq]
  refine ⟨δ, ?_⟩
  intro r
  change e (Dw (e.symm _)) = _
  rw [← he r, e.symm_apply_apply, hext, he]

end RingTheory
