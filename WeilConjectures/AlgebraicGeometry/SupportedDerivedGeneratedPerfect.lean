/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import WeilConjectures.AlgebraicGeometry.SupportedDerivedGeneratedPerfectCore

/-! # Building supported derived objects from a perfect complex

Coproducts are specified by colimiting cofans, so the statement does not require a chosen
coproduct instance. Distinguished triangles are taken in the ambient derived category;
the sequence objects lie in its full quasi-coherent subcategory.

## References

* [Stacks Project, Tag 0E4G](https://stacks.math.columbia.edu/tag/0E4G)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

/-- Every quasi-coherent derived object supported off a quasi-compact open is built from
one perfect supported complex by successive cones and a sequential homotopy colimit.
-/
theorem supported_derived_generated_perfect (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
    ∃ E : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y E.obj ∧
      (∀ (k : ℤ) (y : Y), y ∈ V →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj E.obj).val.presheaf y))) ∧
      ∀ Q : schemeDerivedQCohCategory Y,
        (∀ (k : ℤ) (y : Y), y ∈ V →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf y))) →
        ∃ (X : ℕ → schemeDerivedQCohCategory Y)
          (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj),
          IsZero (X 0).obj ∧
          (∀ n : ℕ, ∃ (I : Type u) (m : I → ℤ)
            (C : Cofan (fun i : I ↦ E.obj⟦m i⟧)), Nonempty (IsColimit C) ∧
            ∃ (a : (X (n + 1)).obj ⟶ C.pt)
              (b : C.pt ⟶ (X n).obj⟦(1 : ℤ)⟧),
              Triangle.mk (t n) a b ∈ distTriang (schemeDerivedCategory Y)) ∧
          ∃ (S : Cofan (fun n : ℕ ↦ (X n).obj)), Nonempty (IsColimit S) ∧
            ∃ (s : S.pt ⟶ S.pt) (q : S.pt ⟶ Q.obj)
              (r : Q.obj ⟶ S.pt⟦(1 : ℤ)⟧),
              (∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1)) ∧
              Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang (schemeDerivedCategory Y) := by
  obtain ⟨htri, ⟨E, hEperf, hEsupp, hdet⟩⟩ :=
    supported_perfect_generator Y (V : Set Y)ᶜ (by
      simpa using V.isOpen.isClosed_compl) (by simpa using hV)
  refine ⟨E, hEperf, ?_, ?_⟩
  · intro k y hy
    exact hEsupp k y (by simpa using hy)
  · intro Q hQ
    apply supported_derived_generated_perfect_core Y V E Q htri
      (perfectObjectCompact Y E hEperf) hEsupp
    · intro K hK
      exact hdet K (fun k y hy ↦ hK k y (by
        simpa only [Set.mem_compl_iff, not_not, SetLike.mem_coe] using hy))
    · intro k y hy
      exact hQ k y (by simpa only [Set.mem_compl_iff, not_not, SetLike.mem_coe] using hy)

end AlgebraicGeometry
