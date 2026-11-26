/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.FlatLocalDepthFormula

/-!
# Depth formula at a prime of a fibre ring

For a flat map `R → S` of Noetherian rings, a prime `p` of `R` and a prime `Q` of the fibre
ring over `p`, the depth of `S` at the contraction of `Q` is the depth of `R_p` plus the depth
of the fibre ring at `Q`.

## Implementation details

The proof localizes at `p` and at the contraction `q` of `Q`, applies the flat local depth
formula to `R_p → S_q`, and identifies the closed fibre `S_q / p S_q` with the localization
of the fibre ring at `Q`. Ring isomorphisms preserve depth.

## References

* [Stacks, Tag 0339]
* [Stacks, Tag 0337]
* [Stacks, Tag 00ON]
* [Stacks, Tag 0H9M]
-/

@[expose] public section

universe u v

namespace RingHom

private theorem maximal_smul_top_ne_top (A : Type*) [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change (IsLocalRing.maximalIdeal A).map (algebraMap A A) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top

private theorem depth_le_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A ≤ IsLocalRing.depth (R := B) B := by
  classical
  simp only [IsLocalRing.depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem depth_eq_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A = IsLocalRing.depth (R := B) B :=
  le_antisymm (depth_le_of_ringEquiv e) (depth_le_of_ringEquiv e.symm)


/-- Depth splits into a base term and a fibre term for a flat map: the depth of `S` at the
contraction of a prime `Q` of the fibre ring over `p` is the depth of `R_p` plus the depth of
the fibre ring at `Q`. -/
theorem depth_eq_add_of_flat_fiber {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] (hflat : (algebraMap R S).Flat)
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime] :
    IsLocalRing.depth (R := Localization.AtPrime
        (Q.comap Algebra.TensorProduct.includeRight.toRingHom))
      (Localization.AtPrime (Q.comap Algebra.TensorProduct.includeRight.toRingHom)) =
    IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p) +
      IsLocalRing.depth (R := Localization.AtPrime Q) (Localization.AtPrime Q) := by
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let q : Ideal S := Q.comap Algebra.TensorProduct.includeRight.toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  have : q.LiesOver p := Ideal.LiesOver.of_eq_comap p
    Algebra.TensorProduct.includeRight rfl
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have hf : (algebraMap Rp Sq).Flat := hflat.localRingHom q p (q.over_def p)
  let I : Ideal Sq := (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sq)
  obtain ⟨_, hlocal, _, hd⟩ :=
    IsLocalRing.depth_eq_add_of_flat_local (algebraMap Rp Sq) hf
  have : IsLocalRing (Sq ⧸ I) := hlocal
  have hIeq : I = p.map (algebraMap R Sq) := by
    dsimp [I]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    exact (IsScalarTower.algebraMap_eq R Rp Sq).symm
  let e := (Ideal.Fiber.algEquivAux₂ p Q).toRingEquiv
  have hquot : (p.map (algebraMap R S)).map (algebraMap S Sq) =
      p.map (algebraMap R Sq) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S Sq]
  let e' : Localization.AtPrime Q ≃+* (Sq ⧸ I) :=
    e.trans ((Ideal.quotientEquivAlgOfEq R hquot).toRingEquiv.trans
      (Ideal.quotientEquivAlgOfEq R hIeq.symm).toRingEquiv)
  exact hd.trans (congrArg (IsLocalRing.depth (R := Rp) Rp + ·)
    (depth_eq_of_ringEquiv e').symm)

end RingHom
