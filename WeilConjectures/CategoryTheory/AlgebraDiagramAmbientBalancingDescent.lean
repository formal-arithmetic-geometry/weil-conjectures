/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraDiagramPullbackData
public import WeilConjectures.CategoryTheory.AlgebraDiagramAmbientSpecialization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
/-! # Descent of ambient coefficient balancing from resolving representatives

Source: Stacks 06YU and 07A4; blueprint:
lem-pur-algebra-diagram-ambient-balancing-descent.
-/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u w
open CategoryTheory CategoryTheory.CochainPullback
open SheafOfModules.PullbackTensorCanonical
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}
/-- Equality of the two ambient coefficient maps descends from resolving objects.

Source: Stacks 06YU and 07A4; this is the localization descent in step 3 of
`lem-pur-algebra-diagram-ambient-balancing`.  The two sides are natural in the
derived object.  Every object is isomorphic to the localization of a
flat-term K-flat representative; cancel that isomorphism and use naturality
to transport the representative equality to the chosen object.
(blueprint: lem-pur-algebra-diagram-ambient-balancing-descent).
-/
theorem ambient_balancing_descent
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f)
    (d : CoefficientSquare.{u, u, u, u, u} f)
    (k' : Comparison.{u, u, u, u, u} (changed f d))
    [IsIso f.coefficient] [IsIso d.coefficient']
    [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
    [ExactPullback f] [ExactPullback (changed f d)]
    [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
    (s : ScalarDerivedPresentation.{u, w} d.sourceMap)
    (t : ScalarDerivedPresentation.{u, w} d.targetMap)
    (b : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ f.L ≅
      (changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap)
    (e : ExtensionComparison f d s t)
    (beta : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap)
    (a : Phi f.L.mapDerivedCategory.{w, w} ≅ Psi f.L.mapDerivedCategory.{w, w})
    (hres : ∀ (P : Complex.{u, u, u} R),
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n)) →
      (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom.app
          (s.model.T.obj (DerivedCategory.Q.obj P)) ≫
          (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.map
            (e.hom.app (DerivedCategory.Q.obj P)) =
        (ambientSpecialization f d s t a beta).hom.app (DerivedCategory.Q.obj P))
    (M : DerivedCategory (Modules.{u, u, u} R)) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom.app (s.model.T.obj M) ≫
        (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.map (e.hom.app M) =
      (ambientSpecialization f d s t a beta).hom.app M := by
  sorry
end CategoryTheory.AlgebraDiagramPullback
