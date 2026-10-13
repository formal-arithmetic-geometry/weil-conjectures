/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedAffineSingleMaps

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The explicit cone comparison carries the restricted colimit leg to the
canonical restricted coefficient map.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-affine-single-cone-leg).

Proof: Expand the inverse of the explicit cone isomorphism and the mapped cocone leg.
The inverse factors are the single comparison, the inverse composition comparison for
q and r_i, the composition comparison for r and c_i, and the restricted eH inverse.
Combine the latter with the restricted colimit injection by functoriality.
These are exactly the defining factors of rawAffineRestrictedCoefficient. -/
theorem restrictedAffineSingleConeIso_inv_leg {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    [HasColimit H] (U : S.Etale) (i : Iᵒᵖ) :
      (restrictedAffineSingleConeIso D c F H eH U i).inv ≫
        (restrictedAffineL D c H U).ι.app (op i) =
        ((upperStar AddCommGrpCat.{v + 1}
          ((restrictedAffineCone D c U).π.app i)).mapCochainComplexSingleFunctor 0).hom.app
            ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
              (F i.unop)) ≫
        (CochainComplex.singleFunctor _ 0).map
          (rawAffineRestrictedCoefficient (c.π.app i).left (D.obj i).hom c.pt.hom
            (Over.w (c.π.app i)) (F i.unop) (colimit H)
            ((eH i.unop).inv ≫ colimit.ι H i.unop) U) := by sorry

end AlgebraicGeometry.Etale
