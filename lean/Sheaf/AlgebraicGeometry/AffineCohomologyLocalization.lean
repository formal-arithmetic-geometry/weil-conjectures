/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.AffineCapSectionOpen
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.AffineCohomologyLocalizationZero

/-! # Localization of cohomology on an affine scheme

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, affine-open paragraph of
its proof; Properties, Tags 01PV and 01PW; Cohomology of Schemes, Tag 01XB
(blueprint: lem-sc-invert-s-cohomology-affine-case).
-/

@[expose] public section

universe uAffine

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme the canonical degree-zero fraction comparison is an isomorphism
in every cohomological degree, and both groups vanish in positive degrees.
The canonical formula is expressed as `s^n e(ξ/s^n) = ξ|_U`: multiplication by `s^n`
is induced on cohomology by `F ≅ F ⊗ O_Y → F ⊗ L^n`. On the nonvanishing open it is
invertible, so this says exactly `e(ξ/s^n) = s⁻ⁿ ξ|_U`.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, affine case
(blueprint: lem-sc-invert-s-cohomology-affine-case).
Proof:
1. By lem-sc-affine-cap-section-open, the nonvanishing open `Y_s` is affine.
2. The source theorem `isQuasicoherent_tensorObj` and the tensor-power invertibility
instance give quasi-coherence of every nonnegative numerator twist. Apply
pqf-lem-affine-vanishing on `Y` and `Y_s` (restriction quasi-coherence is handled
inside that declaration). Thus all positive-degree numerator groups, their direct sum
and its fraction quotient, and the target group vanish.
3. For degree zero use new-affine-cohomology-localization-zero, which transports
lem-sc-affine-section-localization (Stacks 01PW). Its formula
`ξ/s^n ↦ s⁻ⁿ ξ` is the displayed cohomology formula under the degree-zero identification
with sections. In positive degrees the unique map between zero groups is the comparison.
The additive isomorphism with this fraction formula is automatically compatible with
scalar multiplication, since restriction and tensor multiplication are linear. -/
theorem affine_cohomology_localization
    (Y : Scheme.{uAffine}) [IsAffine Y]
    (L : Y.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : Y.Modules) [F.IsQuasicoherent] :
    ∃ U : Y.Opens, (U : Set Y) = nonvanishingLocus L s ∧
      ∀ p : ℕ,
        (∃ e : CohomologyFractionPresentation L F s p ⊤ ≃+
            (RingedSpace.openModuleCohomology Y.toRingedSpace p U).obj F,
          ∀ (n : ℕ)
              (t : (RingedSpace.openModuleCohomology Y.toRingedSpace p ⊤).obj
                (F ⊗ L.tensorPow n : Y.Modules)),
            (RingedSpace.openModuleCohomology Y.toRingedSpace p U).map
                (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                  F ⟶ (F ⊗ L.tensorPow n : Y.Modules))
                (e (cohomologyFraction L F s p ⊤ n t)) =
              (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace p
                (homOfLE (le_top : U ≤ ⊤))).app (F ⊗ L.tensorPow n : Y.Modules) t) ∧
        (0 < p → Subsingleton (CohomologyFractionPresentation L F s p ⊤) ∧
          Subsingleton ((RingedSpace.openModuleCohomology Y.toRingedSpace p U).obj F)) := by
  obtain ⟨⟨U, hU, hiff⟩, _⟩ := affine_cap_section_open Y L s ⊤ (isAffineOpen_top Y)
  have hset : (U : Set Y) = nonvanishingLocus L s := by
    ext x
    change x ∈ U ↔
      (TopCat.Presheaf.germ L.val.presheaf ⊤ x trivial) s ∉
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) •
          (⊤ : Submodule (Y.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk L.val.presheaf x))
    simpa using (hiff x)
  refine ⟨U, hset, ?_⟩
  intro p
  constructor
  · by_cases hp : p = 0
    · subst p
      exact affine_cohomology_localization_zero Y L s F U hset
    · have hp' : 0 < p := Nat.pos_of_ne_zero hp
      let : IsAffineOpen U := hU
      have htop (n : ℕ) : Subsingleton ((RingedSpace.openModuleCohomology
          Y.toRingedSpace p ⊤).obj (F ⊗ L.tensorPow n : Y.Modules)) := by
        let := isQuasicoherent_tensorObj F (L.tensorPow n)
        apply subsingleton_openModuleCohomology_of_isAffineOpen Y
          (F ⊗ L.tensorPow n : Y.Modules) ⊤ (isAffineOpen_top Y) p hp'
      have hfrac : Subsingleton (CohomologyFractionPresentation L F s p ⊤) := by
        let : ∀ n : ℕ, Subsingleton ((RingedSpace.openModuleCohomology
            Y.toRingedSpace p ⊤).obj (F ⊗ L.tensorPow n : Y.Modules)) := fun n => htop n
        let DS := DirectSum ℕ (fun n : ℕ =>
          (RingedSpace.openModuleCohomology Y.toRingedSpace p ⊤).obj
            (F ⊗ L.tensorPow n : Y.Modules))
        let : Subsingleton DS := ⟨fun x y => by
          apply DirectSum.ext
          intro n
          exact Subsingleton.elim _ _⟩
        constructor
        intro a b
        induction a using QuotientAddGroup.induction_on with | _ a =>
          induction b using QuotientAddGroup.induction_on with | _ b =>
            rw [← sub_eq_zero]
            apply (QuotientAddGroup.eq_zero_iff _).2
            simp [Subsingleton.elim a b]
      let := hfrac
      let : Subsingleton ((RingedSpace.openModuleCohomology Y.toRingedSpace p U).obj F) :=
        subsingleton_openModuleCohomology_of_isAffineOpen Y F U hU p hp'
      let : Inhabited (CohomologyFractionPresentation L F s p ⊤) := ⟨0⟩
      let : Inhabited ((RingedSpace.openModuleCohomology Y.toRingedSpace p U).obj F) := ⟨0⟩
      let : Unique (CohomologyFractionPresentation L F s p ⊤) :=
        { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
      let : Unique ((RingedSpace.openModuleCohomology Y.toRingedSpace p U).obj F) :=
        { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
      refine ⟨AddEquiv.ofUnique, ?_⟩
      intro n t
      let := isQuasicoherent_tensorObj F (L.tensorPow n)
      let := subsingleton_openModuleCohomology_of_isAffineOpen Y
        (F ⊗ L.tensorPow n : Y.Modules) U hU p hp'
      apply Subsingleton.elim
  · intro hp
    let : IsAffineOpen U := hU
    have htop (n : ℕ) : Subsingleton ((RingedSpace.openModuleCohomology
        Y.toRingedSpace p ⊤).obj (F ⊗ L.tensorPow n : Y.Modules)) := by
      let := isQuasicoherent_tensorObj F (L.tensorPow n)
      exact subsingleton_openModuleCohomology_of_isAffineOpen Y
        (F ⊗ L.tensorPow n : Y.Modules) ⊤ (isAffineOpen_top Y) p hp
    let DS := DirectSum ℕ (fun n : ℕ =>
      (RingedSpace.openModuleCohomology Y.toRingedSpace p ⊤).obj
        (F ⊗ L.tensorPow n : Y.Modules))
    let : ∀ n : ℕ, Subsingleton ((RingedSpace.openModuleCohomology
        Y.toRingedSpace p ⊤).obj (F ⊗ L.tensorPow n : Y.Modules)) := fun n => htop n
    let : Subsingleton DS := ⟨fun x y => by
      apply DirectSum.ext
      intro n
      exact Subsingleton.elim _ _⟩
    have hfrac : Subsingleton (CohomologyFractionPresentation L F s p ⊤) := by
      constructor
      intro a b
      induction a using QuotientAddGroup.induction_on with | _ a =>
        induction b using QuotientAddGroup.induction_on with | _ b =>
          rw [← sub_eq_zero]
          apply (QuotientAddGroup.eq_zero_iff _).2
          simp [Subsingleton.elim a b]
    exact ⟨hfrac, subsingleton_openModuleCohomology_of_isAffineOpen Y F U hU p hp⟩

end AlgebraicGeometry.Scheme.Modules
