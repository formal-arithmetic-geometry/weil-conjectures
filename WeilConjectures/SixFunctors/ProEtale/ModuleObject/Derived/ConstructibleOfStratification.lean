/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover

/-!
# Constructibility is local on stratifications

Let `Λ` be a commutative condensed ring and `Y` a scheme with noetherian underlying space. A
module object `N` over `Λ_Y` is constructible as soon as its restrictions to the strata of a
stratification `S` of `Y` are
(`ProEtale.CondensedRing.isConstructibleModuleObject_of_stratification`): stratifications `Tᵢ`
of the strata witnessing their constructibility compose with the immersions of the strata to a
stratification of `Y`, indexed by the pairs `(i, a)` with `a` a stratum of `Tᵢ`, along which `N`
is pro-étale locally finitely presented.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Constructibility is local on stratifications**: a module object over `Λ` on a scheme with
noetherian underlying space is constructible as soon as its restrictions to the strata of a
stratification are. -/
theorem isConstructibleModuleObject_of_stratification {Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Y] (S : Scheme.Stratification Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (h : ∀ i, IsConstructibleModuleObject (condensedRingObj Λ (S.domain i))
      ((S.immersion i)^*⟦Λ⟧.obj N)) :
    IsConstructibleModuleObject (condensedRingObj Λ Y) N := by
  choose T hT using h
  let e := Fintype.equivFin (Σ i, Fin (T i).n)
  let f (p : Σ i, Fin (T i).n) : (T p.1).domain p.2 ⟶ Y := (T p.1).immersion p.2 ≫ S.immersion p.1
  have hf (p : Σ i, Fin (T i).n) :
      Set.range (f p) = S.immersion p.1 '' (T p.1).stratum p.2 := by
    rw [← (T p.1).range_immersion p.2, ← Set.range_comp]
    rfl
  refine ⟨Stratification.ofNoetherianSpace _ (fun k ↦ Set.range (f (e.symm k))) (fun k ↦ ?_)
    ?_ ?_ _ (fun k ↦ f (e.symm k)) (fun k ↦ inferInstance) (fun k ↦ rfl), fun k ↦ ?_⟩
  · rw [hf]
    exact ((T _).isLocallyClosed_stratum _).image
      (S.immersion _).isEmbedding.isInducing (S.immersion _).isLocallyClosed_range
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ y)
    rw [← S.range_immersion] at hi
    obtain ⟨z, rfl⟩ := hi
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 ((T i).iUnion_stratum_eq_univ ▸ Set.mem_univ z)
    exact Set.mem_iUnion.2 ⟨e ⟨i, a⟩, by
      rw [Equiv.symm_apply_apply, hf]
      exact Set.mem_image_of_mem _ ha⟩
  · intro k l hkl
    simp only [Function.onFun, hf]
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have hne : e.symm k ≠ e.symm l := e.symm.injective.ne hkl
    generalize e.symm k = p at *
    generalize e.symm l = q at *
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    obtain rfl | hij := eq_or_ne i j
    · obtain rfl := (S.immersion i).isEmbedding.injective hzw
      have hab : a ≠ b := fun hab ↦ hne (by rw [hab])
      exact Set.disjoint_left.1 ((T i).pairwise_disjoint_stratum hab.symm) hw hz
    · have hw' : S.immersion j w ∈ S.stratum j := by
        rw [← S.range_immersion]
        exact ⟨w, rfl⟩
      refine Set.disjoint_left.1 (S.pairwise_disjoint_stratum hij.symm) hw' ?_
      rw [← S.range_immersion]
      exact ⟨z, hzw.symm⟩
  · exact isLocallyFinitelyPresented_mapMod_comp Λ _ _ N (hT _ _)

end AlgebraicGeometry.ProEtale.CondensedRing
