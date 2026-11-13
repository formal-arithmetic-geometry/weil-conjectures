/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore
import WeilConjectures.AlgebraicGeometry.PerfectHomTrianglePresentedRowsExact

/-! # The geometric diagram before taking the exact filtered colimit

## References

* Stacks Project, Tags 09RE and 08BW.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Simultaneous stage rows and their comparison with the limit row
(Stacks, Tags 09RE and 08BW). -/
theorem perfect_hom_mayerVietoris_stage_rows
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    : ∃ (S : ComposableArrows (Set.Ici i ⥤ AddCommGrpCat.{max u w}) 4)
        (B : ComposableArrows AddCommGrpCat.{max u w} 4)
        (κ : S ⟶ B ⋙ Functor.const (Set.Ici i))
        (e : ∀ j : Set.Ici i, (S.obj' 2).obj j ≃
          ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q))
        (b : B.obj' 2 ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        S.Exact ∧ B.Exact ∧
        (∀ (j k : Set.Ici i) (hjk : j ≤ k) (f : (S.obj' 2).obj j),
          e k ((S.obj' 2).map (homOfLE hjk) f) =
            perfectStageMap R s j.property hjk (e j f)) ∧
        (∀ (j : Set.Ici i) (f : (S.obj' 2).obj j),
          b ((κ.app ⟨2, by decide⟩).app j f) =
            perfectLimitMap R c s j.property (e j f)) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 0) ⟨B.obj' 0, κ.app ⟨0, by decide⟩⟩) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 1) ⟨B.obj' 1, κ.app ⟨1, by decide⟩⟩) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 3) ⟨B.obj' 3, κ.app ⟨3, by decide⟩⟩) ∧
        PerfectHomLocalMap R c i X s₀ U V
          (colimit.desc (S.obj' 4) ⟨B.obj' 4, κ.app ⟨4, by decide⟩⟩) := by
  obtain ⟨S, B, κ, e, b, hS, hB, hstage, hlimit, he, hκ, h0, h1, h3, h4⟩ :=
    perfect_hom_mayerVietoris_stage_rows_core R c i X s₀ U V hU hV Y t ht s hs P Q hP hQ
  obtain ⟨hexS, hexB⟩ :=
    perfect_hom_triangle_presented_rows_exact S B hS hB hstage hlimit
  exact ⟨S, B, κ, e, b, hexS, hexB, he, hκ, h0, h1, h3, h4⟩

end AlgebraicGeometry
