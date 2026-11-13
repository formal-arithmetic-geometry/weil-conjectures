/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.FiniteRetractSheavesAffineTrivialization
import Mathlib.Data.Int.Interval

/-! # Finite free refinement of a strictly perfect local model

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A strictly perfect representative near a point can be made finite free on a smaller
affine neighbourhood, without changing the represented derived object. -/
theorem exists_finiteFree_refinement_of_isStrictlyPerfect
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    (E : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (hEP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P))
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffine V.toScheme ∧
      ∃ F : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
        (∀ n : ℤ, ∃ r : ℕ, Nonempty (F.X n ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r)))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj F) := by
  classical
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hP
  obtain ⟨V, hxV, hVU, hAffine, hfree⟩ :=
    exists_affine_trivialization_of_finite_retracts X U (Finset.Icc a b) P.X
      (fun n _ ↦ hp n) x hx
  let R := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)
  let F := (R.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨V, hxV, hVU, hAffine, F, ⟨a, b, fun n hn ↦ R.map_isZero (hb n hn)⟩, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ Finset.Icc a b
    · exact hfree n hn
    · have hz : IsZero (F.X n) := R.map_isZero (hb n (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        exact hn))
      let Z := SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin 0))
      have hZ : IsZero Z := by
        apply (IsZero.iff_id_eq_zero Z).2
        apply (SheafOfModules.freeHomEquiv Z).injective
        funext i
        exact Fin.elim0 i.down
      exact ⟨0, ⟨hz.iso hZ⟩⟩
  · obtain ⟨e⟩ := hEP
    let G := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    have : PreservesFiniteLimits (G ⋙ R) := comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (G ⋙ R) := comp_preservesFiniteColimits _ _
    exact ⟨(Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
        (homOfLE hVU))).symm.app E ≪≫
      (Functor.mapDerivedCategoryCompIso G R).symm.app E ≪≫ R.mapDerivedCategory.mapIso e ≪≫
        R.mapDerivedCategoryFactors.app P⟩

end AlgebraicGeometry.Scheme
