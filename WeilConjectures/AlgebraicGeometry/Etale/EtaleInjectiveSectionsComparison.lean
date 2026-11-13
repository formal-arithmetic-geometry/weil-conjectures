/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
public import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleSectionsTriangleNaturality

/-! # Termwise sections and derived pullback cohomology

Source: Stacks Project, Tag 03Q9, final injective-complex restriction paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The comparison from termwise sections to stage hypercohomology is invertible,
and intertwines both neighbourhood and cone restrictions. This theorem concerns
only the derived-sections unit and its naturality, not derived Hom or the mate.
Source: Stacks, Tag 03Q9, final injective-complex paragraph. -/
theorem smallModel_injectiveSections_strictLocal_comparison {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      IsIso (representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app i) q n)) ∧
    (∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
      representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app j) q n ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj j) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          ((strictLocalNeighbourhoodDiagram f s).map a)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        j)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app j)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map a)
        ((strictLocalNeighbourhoodProjection f s).app j)
            ((strictLocalNeighbourhoodProjection f s).app i) ((Category.comp_id
        ((strictLocalNeighbourhoodProjection f s).app i)).symm.trans
        ((strictLocalNeighbourhoodProjection f s).naturality a).symm)) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app j))
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).map
        a))).symm).inv.app K.obj) =
        termwiseSectionsRestriction ((strictLocalNeighbourhoodDiagram f s).map a)
          ((strictLocalNeighbourhoodProjection f s).app j)
          ((strictLocalNeighbourhoodProjection f s).app i)
          ((Category.comp_id _).symm.trans
            ((strictLocalNeighbourhoodProjection f s).naturality a).symm)
          (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
        representativeSectionsComparison
          ((strictLocalNeighbourhoodProjection f s).app i) q n) ∧
    (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      representativeSectionsComparison
        ((strictLocalNeighbourhoodProjection f s).app i) q n ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (Q.smallModelLegs.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (pullback f (Scheme.strictHenselizationStructuralMap
        s)) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
        ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
        (Scheme.strictHenselizationStructuralMap s))
            (Q.smallModelOver i).symm) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i))).symm).inv.app K.obj) =
        termwiseSectionsRestriction (Q.smallModelLegs.app i)
          ((strictLocalNeighbourhoodProjection f s).app i)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
          (Q.smallModelOver i).symm
          (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
        representativeSectionsComparison
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n) := by
  have h := injectiveSections_strictLocal_comparison f s K n Q J q
  refine ⟨h.1, h.2.1, ?_⟩
  intro i
  exact sectionsComparison_triangle_naturality (Q.smallModelLegs.app i)
    ((strictLocalNeighbourhoodProjection f s).app i)
    (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm
    _ q n

end AlgebraicGeometry.Etale
