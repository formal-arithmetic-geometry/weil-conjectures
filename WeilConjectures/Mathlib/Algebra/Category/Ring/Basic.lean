/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals along isomorphisms of `CommRingCat`

`CommRingCat.hom_mem_ideal_map_iso_iff` and `CommRingCat.ideal_comap_inv_hom` record
that pushing an ideal forward along an isomorphism of commutative rings is the same as
pulling it back along the inverse, in membership and in ideal form.
-/

@[expose] public section

universe u

open CategoryTheory

/-- Membership in the image of an ideal under an isomorphism of commutative rings. -/
lemma CommRingCat.hom_mem_ideal_map_iso_iff {R S : CommRingCat.{u}} (e : R ≅ S)
    (P : Ideal R) (x : R) : e.hom.hom x ∈ P.map e.hom.hom ↔ x ∈ P := by
  conv_rhs =>
    rw [← Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso e.hom)
      (I := P)]
  exact Iff.rfl

/-- Pullback of ideals along the inverse of an isomorphism of commutative rings is
pushforward along the isomorphism. -/
lemma CommRingCat.ideal_comap_inv_hom {R S : CommRingCat.{u}} (e : R ≅ S)
    (I : Ideal R) : I.comap e.inv.hom = I.map e.hom.hom := by
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_)
  · have hxeq : e.hom.hom (e.inv.hom x) = x :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e.inv_hom_id) x
    exact hxeq ▸ Ideal.mem_map_of_mem _ hx
  · have hxeq : e.inv.hom (e.hom.hom x) = x :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e.hom_inv_id) x
    simpa only [Ideal.mem_comap, hxeq] using hx
