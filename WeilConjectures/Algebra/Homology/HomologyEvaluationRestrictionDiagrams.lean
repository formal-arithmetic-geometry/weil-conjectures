/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Homology.OpenOverInternalHomComparison
import WeilConjectures.Algebra.Homology.OpenOverHomComplexCycleProjectionComparison
import WeilConjectures.Algebra.Homology.OpenOverInternalHomCycleHomologySquares

/-! # Restriction comparisons for the cycle-evaluation diagram

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory


private theorem map_three_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {S U V Z : C} {S' U' V' Z' : D}
    (a : S ⟶ U) (b : U ⟶ V) (d : V ⟶ Z)
    (a' : S' ⟶ U') (b' : U' ⟶ V') (d' : V' ⟶ Z')
    (c : F.obj S ⟶ S') (e : F.obj V ⟶ V') (t : F.obj Z ⟶ Z')
    (h1 : F.map (a ≫ b) ≫ e = c ≫ a' ≫ b')
    (h2 : F.map d ≫ t = e ≫ d') :
    F.map (a ≫ b ≫ d) ≫ t = c ≫ a' ≫ b' ≫ d' := by
  simp only [Functor.map_comp, Category.assoc] at h1 ⊢
  rw [h2]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ d') h1

set_option backward.isDefEq.respectTransparency true in
/-- Restriction identifies the cycle-evaluation diagram before choosing any evaluation
map on homology. -/
theorem homologyEvaluation_restriction_diagrams (X : Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (V : X.Opens) (W : V.toScheme.Opens) :
    let F := Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let P := homComplex (R := X.sheaf) T J
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let Q := homComplex (R := V.toScheme.sheaf.over W) A K
    let π := (Classical.choose
      (homComplex_projections_exists (R := V.toScheme.sheaf.over W)))
      A K n (-n) 0 (by omega)
    ∃ a : F.obj (P.homology n) ≅ Q.homology n,
      ∃ b : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.homology (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
      ∃ c : F.obj (P.cycles n) ≅ Q.cycles n,
      ∃ s : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.cycles 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.cycles 0),
      ∃ t : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.X 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.X 0),
      ∃ v : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.homology 0),
        F.map (P.iCycles n ≫ homologyEvaluationProjection X T J n ≫
            SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 _)) ≫ t.hom =
          c.hom ≫ Q.iCycles n ≫ π ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (A.iCycles (-n)) (𝟙 _) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.iCycles 0)) ≫ t.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.iCycles 0) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.homologyπ 0)) ≫ v.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.homologyπ 0) ∧
        F.map (P.homologyπ n) ≫ a.hom = c.hom ≫ Q.homologyπ n ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (T.homologyπ (-n)) (𝟙 _)) ≫
            v.hom = b.hom ≫ SheafOfModules.homObjMap
              (R := V.toScheme.sheaf.over W) (A.homologyπ (-n)) (𝟙 _) := by
  classical
  exact (openOver_internalHom_comparison X V W).elim fun e he ↦
    (openOver_homComplex_cycle_projection_comparison X V W e he T J n).elim fun a ha ↦
      ha.elim fun c hcs ↦
        (openOver_internalHom_cycle_homology_squares X V W e he T J n).elim fun b hb ↦
          hb.elim fun s hs ↦ hs.elim fun t ht ↦ ht.elim fun v hv ↦
            ⟨a, b, c, s, t, v,
              map_three_square _ _ _ _ _ _ _ _ _ _ hcs.1 hv.1,
              hv.2.1, hv.2.2.1, hcs.2, hv.2.2.2⟩

end CategoryTheory
