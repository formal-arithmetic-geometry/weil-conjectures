/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Height formula at a prime of a fibre ring

For a flat map `R → S` of Noetherian rings, a prime `p` of `R` and a prime `Q` of the fibre
ring over `p` lying over `q` in `S`, we have `q.height = p.height + Q.height`.

## Main results

* `RingHom.height_eq_add_of_flat_fiber`

## References

* [Stacks Project, Tag 0339](https://stacks.math.columbia.edu/tag/0339),
  [Tag 0337](https://stacks.math.columbia.edu/tag/0337),
  [Tag 00ON](https://stacks.math.columbia.edu/tag/00ON) and
  [Remark 0H9M](https://stacks.math.columbia.edu/tag/0H9M).
-/

@[expose] public section

universe u v

namespace RingHom

/-- For a flat map `R → S` of Noetherian rings, a prime `p` of `R` and a prime `Q` of the
fibre ring `p.Fiber S`, the prime `q` of `S` under `Q` satisfies
`q.height = p.height + Q.height`. -/
theorem height_eq_add_of_flat_fiber {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] (hflat : (algebraMap R S).Flat)
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime] :
    (Q.comap Algebra.TensorProduct.includeRight.toRingHom).height = p.height + Q.height := by
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let q : Ideal S := Q.comap Algebra.TensorProduct.includeRight.toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  have : q.LiesOver p := Ideal.LiesOver.of_eq_comap p
    Algebra.TensorProduct.includeRight rfl
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have hf : (algebraMap Rp Sq).Flat := hflat.localRingHom q p (q.over_def p)
  have : Module.Flat Rp Sq := RingHom.flat_algebraMap_iff.mp hf
  let I : Ideal Sq := (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sq)
  have hI : I ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (algebraMap Rp Sq)).ne
  have : Fact (I ≠ ⊤) := ⟨hI⟩
  have : Nontrivial (Sq ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (Sq ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal Rp) (IsLocalRing.maximalIdeal Sq)
  have hmap := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hIeq : I = p.map (algebraMap R Sq) := by
    dsimp [I]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    exact (IsScalarTower.algebraMap_eq R Rp Sq).symm
  let e := (Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv
  have hquot : (p.map (algebraMap R S)).map (algebraMap S Sq) =
      p.map (algebraMap R Sq) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S Sq]
  let e' : Localization.AtPrime Q ≃+* (Sq ⧸ p.map (algebraMap R Sq)) :=
    e.trans (Ideal.quotientEquivAlgOfEq R hquot).toRingEquiv
  have hdim : ringKrullDim (Sq ⧸ I) = Q.height := by
    have hi := (Ideal.quotientEquivAlgOfEq R hIeq).toRingEquiv.ringKrullDim
    exact hi.trans (e'.ringKrullDim.symm.trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)))
  rw [hmap] at hheight
  have hheight' := congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hheight
  simp only [WithBot.coe_add] at hheight'
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim,
    IsLocalization.AtPrime.ringKrullDim_eq_height q Sq,
    IsLocalization.AtPrime.ringKrullDim_eq_height p Rp] at hheight'
  exact WithBot.coe_eq_coe.mp hheight'


end RingHom
