/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!
# Finite biproducts of flat objects

A finite biproduct of flat objects of an abelian monoidal preadditive category is flat.

## Main results

- `CategoryTheory.exactFunctor_of_sum_comp_eq_id`: an additive functor which is a finite
  "biproduct" of exact additive functors, in the sense that its identity is a sum of
  composites through them, is exact.
- `CategoryTheory.ObjectProperty.flat_biproduct`: a finite biproduct of flat objects is flat.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- Let `G` be an additive functor between abelian categories whose identity factors as a
finite sum `∑ i, π i ≫ ι i` of composites through exact additive functors `F i`. Then `G`
is exact.

Proof: for an exact short complex `S`, the identity of the homology of `S.map G` is the sum
of the maps induced by `π i ≫ ι i`, each of which factors through the homology of the exact
short complex `S.map (F i)`, which vanishes. -/
lemma exactFunctor_of_sum_comp_eq_id {I : Type*} [Fintype I] (G : A ⥤ B) [G.Additive]
    (F : I → A ⥤ B) [∀ i, (F i).Additive] (π : ∀ i, G ⟶ F i) (ι : ∀ i, F i ⟶ G)
    (htotal : ∑ i, π i ≫ ι i = 𝟙 G) (hF : ∀ i, exactFunctor A B (F i)) :
    exactFunctor A B G := by
  rw [exactFunctor_iff]
  refine (G.exact_tfae.out 1 3).1 fun S hS ↦ ?_
  have hFS (i : I) : (S.map (F i)).Exact := by
    have h := (F i).exact_tfae.out 1 3
    exact h.2 ⟨(hF i).1, (hF i).2⟩ S hS
  have happ (X : A) : ∑ i, (π i).app X ≫ (ι i).app X = 𝟙 (G.obj X) := by
    simpa [NatTrans.app_sum] using NatTrans.congr_app htotal X
  have hid : 𝟙 (S.map G) = ∑ i, S.mapNatTrans (π i) ≫ S.mapNatTrans (ι i) := by
    ext <;> simp only [ShortComplex.id_τ₁, ShortComplex.id_τ₂, ShortComplex.id_τ₃,
      ShortComplex.sum_τ₁, ShortComplex.sum_τ₂, ShortComplex.sum_τ₃, ShortComplex.comp_τ₁,
      ShortComplex.comp_τ₂, ShortComplex.comp_τ₃, ShortComplex.mapNatTrans_τ₁,
      ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃] <;> exact (happ _).symm
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero,
    ← ShortComplex.homologyMap_id, hid, ← ShortComplex.homologyFunctor_map,
    Functor.map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Functor.map_comp, ((ShortComplex.exact_iff_isZero_homology _).1 (hFS i)).eq_of_tgt
    ((ShortComplex.homologyFunctor B).map (S.mapNatTrans (π i))) 0]
  exact zero_comp

namespace ObjectProperty

variable [HasFiniteBiproducts A] [MonoidalCategory A] [MonoidalPreadditive A]

/-- A finite biproduct of flat objects of an abelian monoidal preadditive category is flat.

Proof: tensoring is additive in each variable, so the identity of `tensorLeft (⨁ f)` is the
sum of the composites `tensorLeft (⨁ f) ⟶ tensorLeft (f i) ⟶ tensorLeft (⨁ f)` induced by
the biproduct projections and inclusions, and similarly on the right; apply
`exactFunctor_of_sum_comp_eq_id`. -/
lemma flat_biproduct {I : Type} [Finite I] (f : I → A) (hf : ∀ i, flat (f i)) :
    flat (⨁ f) := by
  have := Fintype.ofFinite I
  refine ⟨exactFunctor_of_sum_comp_eq_id _ (fun i ↦ tensorLeft (f i))
    (fun i ↦ (curriedTensor A).map (biproduct.π f i))
    (fun i ↦ (curriedTensor A).map (biproduct.ι f i)) ?_ fun i ↦ (hf i).1,
    exactFunctor_of_sum_comp_eq_id _ (fun i ↦ tensorRight (f i))
    (fun i ↦ (curriedTensor A).flip.map (biproduct.π f i))
    (fun i ↦ (curriedTensor A).flip.map (biproduct.ι f i)) ?_ fun i ↦ (hf i).2⟩
  · ext X
    simp only [NatTrans.app_sum, NatTrans.comp_app, curriedTensor_map_app, NatTrans.id_app,
      ← comp_whiskerRight]
    rw [← sum_whiskerRight, biproduct.total]
    exact id_whiskerRight _ _
  · ext X
    simp only [NatTrans.app_sum, NatTrans.comp_app, Functor.flip_map_app,
      curriedTensor_obj_map, NatTrans.id_app, ← MonoidalCategory.whiskerLeft_comp,
      ]
    rw [← whiskerLeft_sum, biproduct.total]
    exact whiskerLeft_id _ _

end ObjectProperty

end CategoryTheory
