/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalageComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import all Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries

/-! # Shifted cycle complexes have the original cohomology images

Source: Stacks Project, Homology, Tag 012K, and Derived Categories, Tag 015X.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem cycles_image_of_mono {V K : CochainComplex C ℤ}
    (m : V ⟶ K) [Mono m] (n : ℤ) :
    imageSubobject (HomologicalComplex.cyclesMap m n ≫ K.iCycles n) =
      imageSubobject (m.f n) ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ := by
  have hm (i : ℤ) : Mono (m.f i) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).map m)
    infer_instance
  let S := imageSubobject (m.f n) ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥
  have hS : S ≤ Subobject.mk (m.f n) := by
    simpa only [S, imageSubobject_mono] using (inf_le_left : S ≤ imageSubobject (m.f n))
  let a := Subobject.ofLEMk S (m.f n) hS
  have ha : a ≫ m.f n = S.arrow := Subobject.ofLEMk_comp _
  have hz : S.arrow ≫ K.d n (n + 1) = 0 := by
    apply (Subobject.bot_factors_iff_zero _).mp
    apply (pullback_factors_iff _ _ _).mp
    exact Subobject.factors_right_of_inf_factors S.factors_self
  have had : a ≫ V.d n (n + 1) = 0 := by
    apply (cancel_mono (m.f (n + 1))).mp
    rw [Category.assoc, ← m.comm, ← Category.assoc, ha, hz, zero_comp]
  let t := V.liftCycles a (n + 1) (by simp) had
  apply le_antisymm
  · apply le_inf
    · rw [HomologicalComplex.cyclesMap_i]
      exact imageSubobject_comp_le _ _
    · apply (Subobject.imageSubobject_le_iff _ _).mpr
      apply (pullback_factors_iff _ _ _).mpr
      apply (Subobject.bot_factors_iff_zero _).mpr
      simp
  · change S ≤ _
    rw [HomologicalComplex.cyclesMap_i, imageSubobject_mono]
    apply Subobject.le_mk_of_comm t
    rw [← Category.assoc, HomologicalComplex.liftCycles_i]
    exact ha

/-- The shifted cycle construction changes the boundary presentation but not the image
in ambient cohomology: cycles in `Dec(L)^a` in degree `n` are precisely the ambient
cycles in `L^(a+n)`.
Source: Stacks Project, Tags 012K and 015X
(blueprint: lem-sp-filtered-complex-decalage-image).

Proof. For any monomorphism of complexes V into K, the image of its cycle inclusion
in K^n is im(V^n) intersect ker(d^n). This follows from the universal property of the
kernel: a map into the intersection lifts uniquely to V and is killed by its outgoing
differential. For Dec(L)^a the degree-n image is L^(a+n) intersect the inverse image
of L^(a+n+1) under d. Intersecting with ker(d) removes that inverse-image condition,
since zero belongs to every filtration step. Thus Dec(L)^a and L^(a+n) have the same
cycle subobject inside K^n, hence inside Z^n(K), whose inclusion is monic. Apply the
image functor along the cycle-to-cohomology projection. Its naturality and its
surjectivity on the source complexes identify these images with the two homology-map
images. This proof has no boundedness, first-quadrant, or finite-filtration assumption. -/
theorem decalage_image (K : CochainComplex C ℤ) (L : DecreasingFiltration K) (a n : ℤ) :
    imageSubobject (HomologicalComplex.homologyMap (L.decalageι a) n) =
      imageSubobject (HomologicalComplex.homologyMap (L.step (a + n)).arrow n) := by
  have hs : imageSubobject ((L.decalageι a).f n) ⊓
      (Subobject.pullback (K.d n (n + 1))).obj ⊥ =
      L.complexStep (a + n) n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ := by
    rw [decalageι_image, decalageStep, decalage_complexStep, inf_assoc]
    congr 1
    apply inf_eq_right.mpr
    exact leOfHom ((Subobject.pullback (K.d n (n + 1))).map
      (homOfLE (bot_le : (⊥ : Subobject (K.X (n + 1))) ≤
        L.complexStep (a + n + 1) (n + 1))))
  have hcyc : imageSubobject (HomologicalComplex.cyclesMap (L.decalageι a) n) =
      imageSubobject (HomologicalComplex.cyclesMap (L.step (a + n)).arrow n) := by
    apply Subobject.map_obj_injective (K.iCycles n)
    rw [← Subobject.exists_iso_map, exists_image, exists_image,
      cycles_image_of_mono, cycles_image_of_mono]
    exact hs
  have h := congrArg (fun S ↦ (Subobject.«exists» (K.homologyπ n)).obj S) hcyc
  simpa only [exists_image, ← HomologicalComplex.homologyπ_naturality,
    imageSubobject_comp_of_epi] using h

end CategoryTheory.DecreasingFiltration
