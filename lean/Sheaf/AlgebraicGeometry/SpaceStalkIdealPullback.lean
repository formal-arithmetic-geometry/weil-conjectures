/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.SpaceStalkQuotientTensorData
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.Ideal.Maps

import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.Algebra.Homology.RingedSitePointExact

/-! # Geometric stalk calculation for square-zero algebraic-space immersions

Source: Stacks Project, Properties of Spaces, Tags 04K2, 04K5 and 05VQ;
Modules on Sites, Tags 04EQ and 05V5; Morphisms of Spaces, Tag 03MB;
More on Morphisms of Spaces, Tag 05ZS
(blueprint: lem-sfb-space-stalk-ideal-pullback).

The auxiliary structures are normalized presentations of the objects in this
statement. A stalk includes its actual pointed-neighbourhood colimit cocone;
every ring, module and tensor comparison is prescribed on germs. The theorem
asserts existence of the presentations and all the comparisons together.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace

/-- All normalized comparisons for one square and all its geometric points. 
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: lem-sfb-space-stalk-ideal-pullback). -/
structure SquareZeroSquareCalculation {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X ⟶ X') (j : Y ⟶ Y')
    (h : f ≫ j = i ≫ f') (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
    (I : SquareZeroIdeal W) (J : SquareZeroIdeal T) where
  thickMap : ChartRingMap f W.rings T.rings
  reduces : thickMap.Reduces T W
  induced : thickMap.InducedBy T W f'
  idealMap : (moduleTensorPullback f).obj I.obj ⟶ J.obj
  idealMap_normalization (U : X.EtaleSite) (V : Y.EtaleSite)
    (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom)
    (b : T.rings.obj (op U)) (m : I.obj.val.obj (op V)) :
    J.inclusion U
      (idealMap.val.app (op U)
        (moduleTensorSection f I.obj V
          (CostructuredArrow.mk (CostructuredArrow.homMk a ha.symm))
            (T.quotient.app (op U) b) m)) = b * thickMap.app U V a ha (I.inclusion V m)
  lift_independence (U : X.EtaleSite) (V : Y.EtaleSite)
    (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom)
    (b c : T.rings.obj (op U)) (m : I.obj.val.obj (op V)) :
    T.quotient.app (op U) b = T.quotient.app (op U) c →
    b * thickMap.app U V a ha (I.inclusion V m) =
      c * thickMap.app U V a ha (I.inclusion V m)
  sourceStalks : SquareZeroStalkFamily X (squareZeroStructure X)
  targetStalks : SquareZeroStalkFamily Y (squareZeroStructure Y)
  sourceThickStalks : SquareZeroStalkFamily X (squareZeroThickenedStructure T)
  targetThickStalks : SquareZeroStalkFamily Y (squareZeroThickenedStructure W)
  pointCalculation (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj) :
    SquareZeroPointCalculation f T W I J thickMap (CostructuredArrow.mk s)
      (sourceStalks.stalk Ω b s) (targetStalks.stalk Ω b (s ≫ f.hom.hom))
      (sourceThickStalks.stalk Ω b s) (targetThickStalks.stalk Ω b (s ≫ f.hom.hom))
  pointMap (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj) :
    squareZeroTensor (pointCalculation Ω b s).reducedMap
      ((targetStalks.stalk Ω b (s ≫ f.hom.hom)).modules.obj I.obj.val) →+
        (sourceStalks.stalk Ω b s).modules.obj J.obj.val
  pointMap_smul (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
    (a : (sourceStalks.stalk Ω b s).ring)
    (t : squareZeroTensor (pointCalculation Ω b s).reducedMap
      ((targetStalks.stalk Ω b (s ≫ f.hom.hom)).modules.obj I.obj.val)) :
    pointMap Ω b s (squareZeroTensorScale (pointCalculation Ω b s).reducedMap _ a t) =
      a • pointMap Ω b s t
  pointMap_stalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
    (v : (sourceStalks.stalk Ω b s).modules.obj
      ((moduleTensorPullback f).obj I.obj).val) :
    pointMap Ω b s ((pointCalculation Ω b s).tensorComparison v) =
      (sourceStalks.stalk Ω b s).modules.map idealMap.val v
  pointMap_tmul (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
    (m : (targetStalks.stalk Ω b (s ≫ f.hom.hom)).modules.obj I.obj.val)
    (v : (sourceThickStalks.stalk Ω b s).ring) :
    (pointCalculation Ω b s).inclusionJ
      (pointMap Ω b s (squareZeroTmul (pointCalculation Ω b s).reducedMap _ m
        ((pointCalculation Ω b s).quotientX v))) =
      (pointCalculation Ω b s).thickMap ((pointCalculation Ω b s).inclusionI m) * v
  fibreIdeal (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj) :
    SquareZeroFibreProductIdeal f f' i j h T (CostructuredArrow.mk s)
      (sourceThickStalks.stalk Ω b s)
  fibreIdeal_eq (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj) :
    RingHom.ker (fibreIdeal Ω b s).restriction =
      Ideal.map (pointCalculation Ω b s).thickMap
        (RingHom.ker (pointCalculation Ω b s).quotientY)
  cartesian_iff : IsIso (squareZeroPullbackMap f f' i j h) ↔
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
      (s : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      RingHom.ker (pointCalculation Ω b s).quotientX =
        Ideal.map (pointCalculation Ω b s).thickMap
          (RingHom.ker (pointCalculation Ω b s).quotientY)

/-- The complete geometric stalk calculation, including its canonical ideal map.
Source: Stacks, Tags 04K5, 04K2, 05VQ, 04EQ, 05V5, 03MB, 0DK1 and 05ZS
(blueprint: lem-sfb-space-stalk-ideal-pullback).

Proof:
1. A square-zero closed immersion is a thickening on every affine scheme test.
Use lem-sfb-space-thickening-base-change and
lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism, followed by
lem-sfb-space-integral-radicial-etale-invariance. Coverings agree because the
base-change projections are homeomorphisms. The small-site interpretation is
lem-trf-space-enlarged-etale-ringed-site-model. This gives T and W.
2. On an affine chart Spec R the quotient is Spec (R/K). The section formula
lem-trf-space-etale-module-pushforward-restriction identifies the direct image
of its structure sheaf with R/K. Affine charts cover every object, so the
quotient is locally surjective with its defining kernel. Square-zero
multiplication descends to the quotient module action, giving I and J.
3. Apply lem-sfb-space-geometric-points-conservative and
lem-sfb-ringed-site-point-exact to these quotient sequences. This gives exact
conservative module stalks and the surjective quotient ring square with the
specified kernels. Products of kernel germs are zero after representing them
on a common neighbourhood. The first isomorphism theorem gives the two
normalized quotient ring identifications.
4. The composite point is the image geometric point, by
lem-sfb-space-geometric-points-conservative. Apply
lem-sfb-ringed-topos-pullback-stalk with its pure-tensor normalization. Define
the ideal map by multiplication with any local lift. The difference of lifts
lies in J and kills the image of I, so these maps are independent of the
lift, balanced and compatible with restrictions. Their stalk map is exactly
q(i tensor b) = f'-sharp(i) times any lift of b.
5. By lem-sfb-space-ideal-closed-subspace-correspondence the fibre-product
ideal is the image of the pulled-back ideal. Exact module stalks and the
pullback-stalk comparison identify it with the image of multiplication from
I tensor over A' of B'. Finite sums of these products are exactly I B'.
No injectivity of tensoring is asserted or used.
6. The square gives an inclusion of this image ideal into J. All geometric
points of X' factor through X, since fields kill square-zero elements. By
lem-sfb-space-geometric-points-conservative equality of these ideals is
equivalent to equality at the points of X. The closed-subspace/ideal
correspondence identifies that equality with equality of X and the fibre
product as closed subspaces of X'. The canonical map is the resulting
isomorphism, since a closed immersion is a monomorphism. Conversely a
canonical isomorphism identifies their kernel ideals. No flatness is used. -/
theorem squareZero_stalk_ideal_pullback {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X ⟶ X') (j : Y ⟶ Y')
    (h : f ≫ j = i ≫ f')
    (hi : IsSpaceFirstOrderThickening i) (hj : IsSpaceFirstOrderThickening j) :
    ∃ (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
      (I : SquareZeroIdeal W) (J : SquareZeroIdeal T),
      Nonempty (SquareZeroSquareCalculation f f' i j h T W I J) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
