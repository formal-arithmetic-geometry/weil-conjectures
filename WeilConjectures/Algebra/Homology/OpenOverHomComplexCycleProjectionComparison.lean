/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Homology.OpenOverHomComplexCycleProjectionCycleSquare
import WeilConjectures.Algebra.Homology.OpenOverHomComplexCycleProjectionHomologySquare

/-! # Cycle projection and quotient comparisons for restricted Hom complexes

Source: Stacks Project, Tags 0A8X and 08DL.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonCategory
    (X : Scheme.{u}) : Category X.Modules :=
  SheafOfModules.instCategory (R := X.ringCatSheaf)
local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonPreadditive
    (X : Scheme.{u}) : Preadditive X.Modules :=
  SheafOfModules.instPreadditive X.ringCatSheaf
noncomputable local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonAbelian
    (X : Scheme.{u}) : Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf

attribute [local irreducible] Scheme.Modules.restrictFunctor SheafOfModules.overFunctor
attribute [local irreducible] homComplexFunctor

set_option profiler true in
set_option maxHeartbeats 800000 in
-- Elaborating the restricted complexes and comparison maps exceeds the default budget.
/-- The projection square on Hom cycles and the cycle-to-homology quotient square.
Source: Stacks Project, Tags 0A8X and 08DL; steps 1 and 2 of the parent plan.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison).

Proof: Restriction preserves products by sectionwise computation and the open-site
equivalence. The limiting fans of the chosen Hom projections and e give a unique
degreewise isomorphism carrying every projection to its e comparison. Naturality
 of e for the two differentials, together with additivity of restriction, gives a
 chain isomorphism h. Restriction is exact: localization preserves finite limits
 and colimits, and overFunctorEquiv transports these properties across the open-site
equivalence. Let z and d be the inverse cycle and homology comparisons for P.
 Set c=z followed by cyclesMapIso h and a=d followed by homologyMapIso h.
 Naturality of cycle inclusions and the projection identity for h give the first
 square. Naturality of the cycle-to-homology quotient for exact functors and chain
 maps gives the second. No cycle comparison for T or J is needed in these squares.
 Empty opens, zero complexes and unbounded complexes obey the same universal
 properties; the product uses every integer index. -/
theorem openOver_homComplex_cycle_projection_comparison (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens)
    (e : ∀ M N : X.Modules,
      (Scheme.Modules.restrictFunctor V.ι ⋙
        SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj
          (SheafOfModules.homObj (R := X.sheaf) M N) ≅
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        ((Scheme.Modules.restrictFunctor V.ι ⋙
          SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj M)
        ((Scheme.Modules.restrictFunctor V.ι ⋙
          SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj N))
    (he : ∀ (M M' N N' : X.Modules) (f : M' ⟶ M) (g : N ⟶ N'),
      (Scheme.Modules.restrictFunctor V.ι ⋙
        SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map
          (SheafOfModules.homObjMap (R := X.sheaf) f g) ≫ (e M' N').hom =
        (e M N).hom ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
          ((Scheme.Modules.restrictFunctor V.ι ⋙
            SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map f)
          ((Scheme.Modules.restrictFunctor V.ι ⋙
            SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map g))
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
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
    ∃ c : F.obj (P.cycles n) ≅ Q.cycles n,
      F.map (P.iCycles n ≫ homologyEvaluationProjection X T J n) ≫
          (e (T.X (-n)) (J.X 0)).hom = c.hom ≫ Q.iCycles n ≫ π ∧
      F.map (P.homologyπ n) ≫ a.hom = c.hom ≫ Q.homologyπ n :=
      by
  intro F P A K Q π
  obtain ⟨h, hp⟩ := openOver_homComplex_chain_projection_iso X V W e he T J n
  obtain ⟨a, c, hc, ha⟩ := openOver_chain_cycle_homology_comparison X V W
    P Q h n
  refine ⟨a, c, ?_, ha⟩
  change h.hom.f n ≫ π = F.map (homologyEvaluationProjection X T J n) ≫
    (e (T.X (-n)) (J.X 0)).hom at hp
  change F.map (P.iCycles n) ≫ h.hom.f n = c.hom ≫ Q.iCycles n at hc
  calc
    _ = F.map (P.iCycles n) ≫ (h.hom.f n ≫ π) := by
      rw [Functor.map_comp, Category.assoc, hp]
    _ = _ := by rw [← Category.assoc, hc, Category.assoc]

end CategoryTheory
