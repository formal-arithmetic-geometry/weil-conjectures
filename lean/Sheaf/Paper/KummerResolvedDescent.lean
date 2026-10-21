/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerCoherentRoof
public import Sheaf.Paper.KummerLocalSource

/-! # Actual total comparisons of augmented Kummer resolutions
Source: direct-image proof (3), augmented finite total followed by internal bar.
(blueprint: def-sfb-kummer-resolved-descent).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- A resolved descent includes the actual augmentation and one coherent roof.
The final comparison is fixed by the displayed total equation, and the bar model
already fixes its invariant inclusion. Source: direct-image proof (3)
(blueprint: def-sfb-kummer-resolved-descent). -/
structure KummerResolvedDescent (B : Model A G) {T W U S : Scheme.{u}}
    (a : W ⟶ U) (s : S ⟶ U) (v : T ⟶ W)
    (L : KummerModules A.X W) (N : Equivariant A G) where
  resolution : InjectiveResolution L
  actionResolution : InjectiveResolution N
  barResolution : KummerBarResolutionData A G B S actionResolution
  augmentation : ((lowerStar A.X a ⋙ upperStar A.X s).mapHomologicalComplex (.up ℕ)).obj
      resolution.cocomplex ⟶ kummerTotal A.X a s v resolution.cocomplex
  augmentation_normalized : IsKummerAugmentation A.X a s v resolution.cocomplex augmentation
  augmentation_iso : IsIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap augmentation ComplexShape.embeddingUpNat))
  roof : KummerCoherentRoof A G B a s v resolution actionResolution
  comparison : kummerOpenImage A.X a s L ≅
    (kummerPointPullBig A S).obj
      (B.invariants.functor.rightDerivedFunctor.{u + 2, u + 2,
        u + 1, u + 1, u + 2, u + 2}.obj
          ((DerivedCategory.singleFunctor.{u + 2} _ 0).obj N))
  normalization :
    (kummerResolutionComparison A.X a s resolution).hom ≫
      DerivedCategory.Q.map
        (HomologicalComplex.extendMap augmentation ComplexShape.embeddingUpNat) ≫
      roof.totalComparison.hom =
    comparison.hom ≫ (kummerBarTotalIso A G B S actionResolution barResolution).inv

end AlgebraicGeometry.ProEtale.CondensedRing
