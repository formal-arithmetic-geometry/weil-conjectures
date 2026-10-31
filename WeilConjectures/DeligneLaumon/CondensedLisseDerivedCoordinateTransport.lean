/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
public import WeilConjectures.DeligneLaumon.CondensedLinePullCoherence

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- Scalar, tensor-power, and derived transport turns a root-coordinate equation into
the shifted Tate-line equation. Source: the transport part of Step 2 of
`thm-a1-curve-perverse-heart`.
(blueprint: lem-per-condensed-lisse-derived-coordinate-transport).
-/
theorem derived_coordinate_transport (k : Type u) [Field k] (hEll : IsUnit (ell : k))
    {W V T : Space k} [Nonempty W.scheme]
    (i : W.scheme ⟶ V.scheme) (j : V.scheme ⟶ T.scheme)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (qi : PurityTransport.LinePullCoordinates ell c i)
    (qj : PurityTransport.LinePullCoordinates ell c j)
    (qij : PurityTransport.LinePullCoordinates ell c (i ≫ j))
    (hroot :
      (CondensedRing.upperStarComp
          (Profinite.continuousMapRingObj ℤ_[ell]) i j).hom.app
          (tateModule T.scheme ell) ≫
          (CondensedRing.upperStar
            (Profinite.continuousMapRingObj ℤ_[ell]) i).map qj.integral.hom ≫
          qi.integral.hom = qij.integral.hom) :
      (pullComp ell c i j).hom.app (c.derivedLine ell T.scheme T.dim.val) ≫
          (pull ell c i).map ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) j).inv.app _ ≫ (qj.derived ell T.dim.val).hom) ≫
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) i).inv.app _ ≫ (qi.derived ell T.dim.val).hom) =
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) (i ≫ j)).inv.app _ ≫ (qij.derived ell T.dim.val).hom) := by sorry

end AlgebraicGeometry.ProEtale.CondensedLisseDual
