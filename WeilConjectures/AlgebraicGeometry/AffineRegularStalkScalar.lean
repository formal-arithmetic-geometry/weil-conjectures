/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFreeBasisGerms
import WeilConjectures.AlgebraicGeometry.AffineScalarSectionAction

/-! # Scalar action on the unit germ of affine sheafification

Source: Stacks Project, Tag 01HV, Lemma 26.5.4, functoriality, and Tag 0098.
-/

@[expose] public section
universe u
namespace AlgebraicGeometry.Scheme

/-- A scalar endomorphism acts on the explicit unit germ by the scalar's germ
(Stacks, Tags 01HV and 0098). -/
theorem affineRegularStalkGerm_scalar
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (a : Γ(X, U)) :
    (affineFreeStalkFunctor X x U hU).map (affineScalarEnd X U a)
        (affineRegularStalkGerm X x U hxU hU) =
      X.presheaf.germ U x hxU a • affineRegularStalkGerm X x U hxU hU := by
  let P := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
  let M := (affinePerfectSheafification X U hU).obj (ModuleCat.of Γ(X, U) Γ(X, U))
  let b := (P.map (affineRegularSheafIso X U hU).inv).val.app (.op U)
    (1 : ((moduleRings X.toRingedSpace).over U).obj.obj
      (.op ((CategoryTheory.Over.star U).obj U)))
  change RingedSpace.stalkAddMap X.toRingedSpace x
    (P.map ((affinePerfectSheafification X U hU).map (affineScalarEnd X U a)))
    (TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU b) = _
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU
    ((P.map ((affinePerfectSheafification X U hU).map
      (affineScalarEnd X U a))).val.app (.op U) b) =
    X.presheaf.germ U x hxU a •
      TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU b
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) (P.obj M).val]
  apply congrArg (TopCat.Presheaf.germ (P.obj M).val.presheaf U x hxU)
  exact affineScalarEnd_section_action X U hU a b

end AlgebraicGeometry.Scheme
