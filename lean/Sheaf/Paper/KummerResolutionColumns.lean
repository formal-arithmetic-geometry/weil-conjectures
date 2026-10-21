/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerNormalizedComparison
public import Sheaf.Paper.ProfiniteConstantDerivedFunctions

/-! # Canonical resolution columns of Kummer descent
Source: direct-image proof (3), compatible resolutions of nerve terms.
(blueprint: def-sfb-kummer-resolution-columns).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A column of a compatible cosimplicial complex.
Source: direct-image proof (3), coherent nerve terms
(blueprint: def-sfb-kummer-resolution-columns). -/
def kummerDiagramColumn (S : Scheme.{u})
    (K : CochainComplex (SimplexCategory ⥤ KummerModules Λ S) ℕ) (n : ℕ) :
    CochainComplex (KummerModules Λ S) ℕ :=
  (((evaluation SimplexCategory (KummerModules Λ S)).obj (.mk n)).mapHomologicalComplex
    (.up ℕ)).obj K

/-- The comparison of a resolved column to its actual derived direct image, with
both the resolution augmentation and right-derived unit retained.
Source: direct-image proof (3), normalized nerve column
(blueprint: def-sfb-kummer-resolution-columns). -/
def kummerImageColumnMap {W V U S : Scheme.{u}}
    (v : V ⟶ W) (q : V ⟶ U) (s : S ⟶ U)
    {L : KummerModules Λ W} (I : InjectiveResolution L) :
    DerivedCategory.Q.obj
        (((upperStar Λ v ⋙ lowerStar Λ q ⋙ upperStar Λ s).mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex
            |>.extend ComplexShape.embeddingUpNat) ⟶
      (upperStar Λ s).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ q).obj
          ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ v).obj L))) := by
  let K := ((upperStar Λ v).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let η : ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ v).obj L)) ≅
      DerivedCategory.Q.obj K :=
    ((upperStar Λ v).mapDerivedCategorySingleFunctor 0).symm.app L ≪≫
      (upperStar Λ v).mapDerivedCategory.mapIso (asIso (DerivedCategory.Q.map I.ι')) ≪≫
      (upperStar Λ v).mapDerivedCategoryFactors.app I.cochainComplex
  exact (DerivedCategory.Q.mapIso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
        (upperStar Λ v ⋙ lowerStar Λ q ⋙ upperStar Λ s))).inv ≫
    ((upperStar Λ s).mapDerivedCategoryFactors.app
      (((lowerStar Λ q).mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
    (upperStar Λ s).mapDerivedCategory.map
      ((lowerStar Λ q).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
    (upperStar Λ s).mapDerivedCategory.map
      ((moduleObjectDerivedPushforward Λ q).map η.inv)

end AlgebraicGeometry.ProEtale.CondensedRing
