/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible
import WeilConjectures.AlgebraicGeometry.FreeCechComplexBlockEquiv
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Fibrewise comparison for the evaluated free Čech complex

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03F5](https://stacks.math.columbia.edu/tag/03F5)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Exactness of the evaluated free Čech complex is equivalent to range/kernel equality
in each tuple complex over a fixed map to the base. This comparison does not assert that
any of the tuple complexes is exact (Stacks, Tags 03AT and 03F5). -/
theorem freeCechComplex_exact_iff_fibres (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) (p : ℕ) :
    (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex (PresheafOfModules.{u} O)).obj
        ((FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
          (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
            (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O)))).ExactAt (p + 1) ↔
      ∀ φ : W ⟶ U₀,
        let S := Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}
        LinearMap.range (Algebra.powerSetComplexDifferential (O.obj (op W)) S (p + 1)) =
          LinearMap.ker (Algebra.powerSetComplexDifferential (O.obj (op W)) S p) := by
  classical
  let K := (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex (PresheafOfModules.{u} O)).obj
        ((FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
          (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
            (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O))))
  let S := fun φ : W ⟶ U₀ => Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}
  let d := fun n : ℕ => DFinsupp.mapRange.linearMap
    (fun φ => Algebra.powerSetComplexDifferential (O.obj (op W)) (S φ) n)
  obtain ⟨e, he⟩ := freeCechComplex_block_equiv X ι U₀ U f O W
  change K.ExactAt (p + 1) ↔ _
  rw [K.exactAt_iff' (p + 2) (p + 1) p (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (K.d (p + 2) (p + 1)).hom =
    LinearMap.ker (K.d (p + 1) p).hom ↔ _
  have ht : LinearMap.range (d (p + 1)) = LinearMap.ker (d p) ↔
      LinearMap.range (K.d (p + 2) (p + 1)).hom =
        LinearMap.ker (K.d (p + 1) p).hom := by
    simpa only [LinearMap.exact_iff, eq_comm] using
      Function.Exact.iff_of_ladder_linearEquiv (he (p + 1)) (he p)
  rw [← ht]
  let a := fun φ => Algebra.powerSetComplexDifferential (O.obj (op W)) (S φ) (p + 1)
  let b := fun φ => Algebra.powerSetComplexDifferential (O.obj (op W)) (S φ) p
  change LinearMap.range (DFinsupp.mapRange.linearMap a) =
    LinearMap.ker (DFinsupp.mapRange.linearMap b) ↔
    ∀ φ, LinearMap.range (a φ) = LinearMap.ker (b φ)
  constructor
  · intro h i
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hx : DFinsupp.single i (a i y) ∈
          LinearMap.range (DFinsupp.mapRange.linearMap a) := by
        exact ⟨DFinsupp.single i y, by simp [DFinsupp.mapRange.linearMap]⟩
      rw [h, LinearMap.mem_ker] at hx
      have := congrArg (fun z => z i) hx
      simpa [DFinsupp.mapRange.linearMap] using this
    · intro hx
      change b i x = 0 at hx
      have hz : DFinsupp.single i x ∈
          LinearMap.ker (DFinsupp.mapRange.linearMap b) := by
        rw [LinearMap.mem_ker]
        simp [DFinsupp.mapRange.linearMap, hx]
      rw [← h] at hz
      obtain ⟨y, hy⟩ := hz
      exact ⟨y i, by simpa [DFinsupp.mapRange.linearMap] using congrArg (fun z => z i) hy⟩
  · intro h
    rw [DFinsupp.range_mapRangeLinearMap, DFinsupp.ker_mapRangeLinearMap]
    simp_rw [h]

end AlgebraicGeometry
