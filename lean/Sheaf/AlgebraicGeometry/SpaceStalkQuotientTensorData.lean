/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData
public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.RingTheory.Ideal.Maps

/-! # Normalized square-zero stalk-comparison data

Source: Stacks Project, Properties of Spaces, Tags 04K2, 04K5 and 05VQ;
Modules on Sites, Tags 04EQ and 05V5; Morphisms of Spaces, Tag 03MB;
More on Morphisms of Spaces, Tag 05ZS
(blueprint: def-sfb-space-stalk-quotient-tensor-data).

These structures record normalized presentations of the objects used in the
geometric stalk calculation. Their defining equations prescribe the comparisons
on germs. This definition module makes no existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace

/-- Kernel identifications and the quotient ring square at a geometric point.
Source: Stacks, Tags 04K2, 04K5, 03MB and 05V5
(blueprint: def-sfb-space-stalk-quotient-tensor-data). -/
structure SquareZeroPointCalculation {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) {i : X ⟶ X'} {j : Y ⟶ Y'}
    (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
    (I : SquareZeroIdeal W) (J : SquareZeroIdeal T)
    (α : ChartRingMap f W.rings T.rings)
    (p : SquareZeroPoint X)
    (sx : SquareZeroStalk p (squareZeroStructure X))
    (sy : SquareZeroStalk ((CostructuredArrow.map f.hom.hom).obj p)
      (squareZeroStructure Y))
    (sx' : SquareZeroStalk p (squareZeroThickenedStructure T))
    (sy' : SquareZeroStalk ((CostructuredArrow.map f.hom.hom).obj p)
      (squareZeroThickenedStructure W)) where
  quotientX : sx'.ring →+* sx.ring
  quotientY : sy'.ring →+* sy.ring
  quotientX_germ (n : SquareZeroNeighborhood p)
    (a : (squareZeroThickenedStructure T).obj (op n.right)) :
    quotientX (sx'.ringGerms.app (op n) a) =
      sx.ringGerms.app (op n) (T.quotient.app (op n.right) a)
  quotientY_germ
    (n : SquareZeroNeighborhood ((CostructuredArrow.map f.hom.hom).obj p))
    (a : (squareZeroThickenedStructure W).obj (op n.right)) :
    quotientY (sy'.ringGerms.app (op n) a) =
      sy.ringGerms.app (op n) (W.quotient.app (op n.right) a)
  quotientX_surjective : Function.Surjective quotientX
  quotientY_surjective : Function.Surjective quotientY
  thickMap : sy'.ring →+* sx'.ring
  reducedMap : sy.ring →+* sx.ring
  thickMap_normalization : SquareZeroRingMap f rfl sx' sy'
    (fun U V a ha b ↦ α.app U V a ha b) thickMap
  reducedMap_normalization : SquareZeroRingMap f rfl sx sy
    (fun _ _ a _ b ↦ Scheme.Γ.map a.left.op b) reducedMap
  commutes : quotientX.comp thickMap = reducedMap.comp quotientY
  inclusionI : sy.modules.obj I.obj.val →+ sy'.ring
  inclusionJ : sx.modules.obj J.obj.val →+ sx'.ring
  inclusionI_germ
    (n : SquareZeroNeighborhood ((CostructuredArrow.map f.hom.hom).obj p))
    (m : I.obj.val.obj (op n.right)) :
    inclusionI ((sy.moduleGerms I.obj.val).app (op n) m) =
      sy'.ringGerms.app (op n) (I.inclusion n.right m)
  inclusionJ_germ (n : SquareZeroNeighborhood p) (m : J.obj.val.obj (op n.right)) :
    inclusionJ ((sx.moduleGerms J.obj.val).app (op n) m) =
      sx'.ringGerms.app (op n) (J.inclusion n.right m)
  inclusionI_injective : Function.Injective inclusionI
  inclusionJ_injective : Function.Injective inclusionJ
  kernelI (a : sy'.ring) : quotientY a = 0 ↔ ∃ m, inclusionI m = a
  kernelJ (a : sx'.ring) : quotientX a = 0 ↔ ∃ m, inclusionJ m = a
  scalarI (a : sy'.ring) (m : sy.modules.obj I.obj.val) :
    inclusionI (quotientY a • m) = a * inclusionI m
  scalarJ (a : sx'.ring) (m : sx.modules.obj J.obj.val) :
    inclusionJ (quotientX a • m) = a * inclusionJ m
  squareZeroI : RingHom.ker quotientY * RingHom.ker quotientY = ⊥
  squareZeroJ : RingHom.ker quotientX * RingHom.ker quotientX = ⊥
  quotientIsoI : sy'.ring ⧸ RingHom.ker quotientY ≃+* sy.ring
  quotientIsoJ : sx'.ring ⧸ RingHom.ker quotientX ≃+* sx.ring
  quotientIsoI_normalization (a : sy'.ring) :
    quotientIsoI (Ideal.Quotient.mk _ a) = quotientY a
  quotientIsoJ_normalization (a : sx'.ring) :
    quotientIsoJ (Ideal.Quotient.mk _ a) = quotientX a
  tensorComparison :
    sx.modules.obj ((moduleTensorPullback f).obj I.obj).val ≃+
      squareZeroTensor reducedMap (sy.modules.obj I.obj.val)
  tensorComparison_smul (b : sx.ring)
    (t : sx.modules.obj ((moduleTensorPullback f).obj I.obj).val) :
    tensorComparison (b • t) =
      squareZeroTensorScale reducedMap (sy.modules.obj I.obj.val) b (tensorComparison t)
  tensorComparison_germ
    (n : SquareZeroNeighborhood p)
    (m : SquareZeroNeighborhood ((CostructuredArrow.map f.hom.hom).obj p))
    (a : n.right.obj.left ⟶ m.right.obj.left)
    (ha : n.right.obj.hom ≫ f.hom.hom = yoneda.map a ≫ m.right.obj.hom)
    (hp : n.hom.left ≫ a = m.hom.left)
    (b : X.structurePresheaf.obj (op n.right)) (v : I.obj.val.obj (op m.right)) :
    tensorComparison
      ((sx.moduleGerms ((moduleTensorPullback f).obj I.obj).val).app (op n)
        (moduleTensorSection f I.obj m.right
          (CostructuredArrow.mk (CostructuredArrow.homMk a ha.symm)) b v)) =
      squareZeroTmul reducedMap (sy.modules.obj I.obj.val)
        ((sy.moduleGerms I.obj.val).app (op m) v) (sx.ringGerms.app (op n) b)

end AlgebraicGeometry.AlgebraicSpace
