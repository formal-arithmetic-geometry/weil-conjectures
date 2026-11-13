/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-! # Degree bound from a finite open cover

## References

* Stacks Project, Tag 03JA
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- The finite open-cover degree estimate is the parenthetical claim in the
proof of Stacks Project Lemma 03JA. -/
/-- A finite open cover by schemes finite over a field makes the whole scheme
finite over that field, with degree bounded by the sum of the piece degrees.
(Stacks, Tag 03JA) -/
theorem finite_open_cover_degree_sum
    {k : Type u} [Field k] {T : Scheme.{u}}
    (t : T ⟶ Spec (.of k)) (m : ℕ) (U : Fin m → T.Opens)
    (n : Fin m → ℕ)
    (hcover : ⨆ i, U i = ⊤)
    (hfinite : ∀ i : Fin m, IsFinite ((U i).ι ≫ t))
    (hbound : ∀ i : Fin m, ((U i).ι ≫ t).finrankΓ ≤ n i) :
    IsFinite t ∧ t.finrankΓ ≤ ∑ i : Fin m, n i := by
  classical
  let (i : Fin m) : IsFinite ((U i).ι ≫ t) := hfinite i
  let := t.ΓAlgebra
  let (i : Fin m) := ((U i).ι ≫ t).ΓAlgebra
  have hB (i : Fin m) : Module.Finite k Γ(U i, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ ((U i).ι ≫ t).appTop).hom).Finite
    rw [CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso]
    exact ((U i).ι ≫ t).finite_appTop
  let (i : Fin m) : Module.Finite k Γ(U i, ⊤) := hB i
  have (i : Fin m) : IsAffine (U i).toScheme :=
    isAffine_of_isAffineHom ((U i).ι ≫ t)
  have (i : Fin m) : DiscreteTopology (Spec Γ(U i, ⊤)) :=
    Algebra.QuasiFinite.discreteTopology_primeSpectrum k Γ(U i, ⊤)
  have (i : Fin m) : Finite (Spec Γ(U i, ⊤)) :=
    finite_of_compact_of_discrete
  have hfin (i : Fin m) : Finite (U i) :=
    Finite.of_injective (U i).toScheme.isoSpec.hom.homeomorph
      (U i).toScheme.isoSpec.hom.homeomorph.injective
  let (i : Fin m) : Finite (U i) := hfin i
  have (i : Fin m) : DiscreteTopology (U i) :=
    (U i).toScheme.isoSpec.hom.homeomorph.isEmbedding.discreteTopology
  have hcov : (⋃ i, (U i : Set T)) = Set.univ := by
    simp only [← TopologicalSpace.Opens.coe_iSup, hcover, TopologicalSpace.Opens.coe_top]
  have hTfin : (Set.univ : Set T).Finite := by
    rw [← hcov]
    exact Set.finite_iUnion fun i ↦ hfin i
  let : Finite T := Set.finite_univ_iff.mp hTfin
  let : DiscreteTopology T := discreteTopology_iff_isOpen_singleton.mpr fun x ↦ by
    have hx : x ∈ ⋃ i, (U i : Set T) := hcov.symm ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have h := (U i).ι.isOpenEmbedding.isOpenMap {⟨x, hi⟩} (isOpen_discrete _)
    simpa using h
  have : IsAffine T := inferInstance
  let ρ (i : Fin m) : Γ(T, ⊤) →ₐ[k] Γ(U i, ⊤) :=
    { toRingHom := (U i).ι.appTop.hom
      commutes' := fun r ↦ by
        change (U i).ι.appTop.hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop).hom r) =
          (((Scheme.ΓSpecIso (.of k)).inv ≫ ((U i).ι ≫ t).appTop).hom r)
        rw [Scheme.Hom.comp_appTop]
        rfl }
  let f : Γ(T, ⊤) →ₗ[k] (∀ i : Fin m, Γ(U i, ⊤)) :=
    LinearMap.pi fun i ↦ (ρ i).toLinearMap
  have hf : Function.Injective f := by
    intro a b hab
    apply TopCat.Sheaf.eq_of_locally_eq' T.sheaf (fun i ↦ (U i).ι ''ᵁ ⊤) ⊤
      (fun _ ↦ homOfLE le_top)
    · simpa using hcover.ge
    · intro i
      exact congrFun hab i
  have : Module.Finite k Γ(T, ⊤) := Module.Finite.of_injective f hf
  refine ⟨?_, ?_⟩
  · rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h : (algebraMap k Γ(T, ⊤)).Finite := RingHom.finite_algebraMap.mpr inferInstance
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop).hom).Finite at h
    rwa [CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso] at h
  · change Module.finrank k Γ(T, ⊤) ≤ ∑ i : Fin m, n i
    calc
      _ ≤ Module.finrank k (∀ i : Fin m, Γ(U i, ⊤)) :=
        LinearMap.finrank_le_finrank_of_injective hf
      _ = ∑ i : Fin m, Module.finrank k Γ(U i, ⊤) := Module.finrank_pi_fintype k
      _ ≤ ∑ i : Fin m, n i := Finset.sum_le_sum fun i _ ↦ hbound i

end AlgebraicGeometry
