/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraDiagramPullbackData
public import WeilConjectures.CategoryTheory.AlgebraDiagramAmbientSpecialization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
/-! # Resolving representative calculation for ambient coefficient balancing

Source: Stacks 03EL and 07A4; blueprint:
lem-pur-algebra-diagram-ambient-balancing-resolving.
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
/-- The normalized ambient balancing equation on a flat-term K-flat representative.

Source: Stacks 03EL and 07A4; this is the two-factor resolving calculation in
step 1 of `lem-pur-algebra-diagram-ambient-balancing`.  Choose the two
resolving factors, expand the normalized extension and ambient equations,
and compare the resulting cochain maps on generalized pure tensors.  The
ordinary generator equations for `b` and `beta`, together with the balancing
relation, identify the two maps.  Sheaf tensor extensionality and localization
then give the displayed equality at the localization of `P`.
(blueprint: lem-pur-algebra-diagram-ambient-balancing-resolving).
-/
theorem ambient_balancing_resolving
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
    (hb : ∀ (H : Modules.{u, u, u} d.R') (Z : Sheaf K (Type u))
      (x : Z ⟶ (underlying.{u, u, u} d.R').obj H),
      generator f k x ≫ (underlying.{u, u, u} S).map (b.hom.app H) =
        generator (changed f d) k' x)
    (e : ExtensionComparison f d s t) (he : IsNormalizedExtension f k d k' s t e)
    (beta : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap)
    (hbeta : ∀ (Z : Sheaf K (Type u))
      (x : Z ⟶ (underlying.{u, u, u} R).obj (coefficient d.sourceMap)),
      generator f k x ≫ (underlying.{u, u, u} S).map beta.hom =
        f.uInv.map x ≫ d.I'.ringUnderlying.hom ≫
          (sheafCompose L (forget CommRingCat.{u})).map d.coefficient')
    (a : Phi f.L.mapDerivedCategory.{w, w} ≅ Psi f.L.mapDerivedCategory.{w, w})
    (ha : IsNormalized f k f.L.mapDerivedCategory f.L.mapDerivedCategoryFactors.hom a.hom)
    (P : Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n)) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom.app
        (s.model.T.obj (DerivedCategory.Q.obj P)) ≫
        (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.map
          (e.hom.app (DerivedCategory.Q.obj P)) =
      (ambientSpecialization f d s t a beta).hom.app (DerivedCategory.Q.obj P) := by
  sorry
end CategoryTheory.AlgebraDiagramPullback
