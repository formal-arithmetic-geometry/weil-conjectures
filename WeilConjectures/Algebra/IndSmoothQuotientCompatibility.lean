/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.Basic

import WeilConjectures.Algebra.IndSmoothRingEquiv

/-!
# Ind-smoothness and successive quotients

## References

* [Stacks Project, Tag 07CM](https://stacks.math.columbia.edu/tag/07CM), proof of the
  proposition, induction on the nilpotence exponent
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

/-- Taking a quotient by `K ≤ I` before reducing by `I` preserves the ind-smoothness
hypothesis on that reduction. -/
theorem ind_smooth_quotient_compatibility
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I K : Ideal R) (hKI : K ≤ I)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)))) :
    let R' := R ⧸ K
    let Λ' := Λ ⧸ K.map (algebraMap R Λ)
    let I' := I.map (Ideal.Quotient.mk K)
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R' ⧸ I') ↦ Smooth (R' ⧸ I') C)
      (CommAlgCat.of (R' ⧸ I') (Λ' ⧸ I'.map (algebraMap R' Λ'))) := by
  dsimp
  let L := K.map (algebraMap R Λ)
  let J := I.map (algebraMap R Λ)
  have hLJ : L ≤ J := Ideal.map_mono hKI
  have hmap : (I.map (Ideal.Quotient.mk K)).map
      (algebraMap (R ⧸ K) (Λ ⧸ L)) = J.map (Ideal.Quotient.mk L) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  let e := DoubleQuot.quotQuotEquivQuotOfLE hKI
  let f : ((Λ ⧸ L) ⧸ (I.map (Ideal.Quotient.mk K)).map
      (algebraMap (R ⧸ K) (Λ ⧸ L))) ≃+* Λ ⧸ J :=
    (Ideal.quotientEquivAlgOfEq Λ hmap).toRingEquiv.trans
      (DoubleQuot.quotQuotEquivQuotOfLE hLJ)
  apply ind_smooth_of_ringEquiv e f.symm _ hΛ
  intro r
  apply f.injective
  rw [f.apply_symm_apply]
  induction r using Quotient.inductionOn with
  | h r =>
    induction r using Quotient.inductionOn with
    | h r =>
      rfl


end Algebra
