/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.LeraySpectralSequence
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Low degree terms of the Leray spectral sequence

Source: blueprint node `pqf-lem-leray-lowdegree`; Stacks Project, Cohomology of Sheaves,
Lemma 20.13.4, Tag 01F2 (blueprint: pqf-lem-leray-lowdegree).
-/

@[expose] public section

universe v

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- (blueprint: pqf-lem-leray-lowdegree)
The low degree five-term exact sequence for the Leray spectral sequence, together with
its degree-one consequence when the first higher direct image vanishes.

The first nonzero arrow is the established module-cohomology edge map.

Source: blueprint node `pqf-lem-leray-lowdegree`; Stacks Project, Cohomology of Sheaves,
Lemma 20.13.4, Tag 01F2.
Proof: apply `CategoryTheory.BigradedExactCouple.lerayFiveTerm` to the first-quadrant
spectral sequence of `exists_leray_spectralSequence`; identify its edge maps with the
canonical Leray maps by `lem-sp-grothendieck-edge-maps`.  The cohomology definitions
identify the terms (pqf-def-cohomology); the zeroth derived direct image identifies
with direct image because it is left exact. The bottom edge is
`Scheme.Modules.moduleCohomologyEdgeMap`. If R¹f_*F is zero, its H⁰ is zero; exactness
then makes the degree-one edge injective and surjective, hence an isomorphism.
-/
theorem lerayLowDegree {X Y : Scheme.{v}} (f : X ⟶ Y)
    (F : SheafOfModules.{v} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent] :
    ∃ (c :
        (forget₂ (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{v}).obj ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj F) ⟶
        (forget₂ (ModuleCat.{v} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{v}).obj
          ((RingedSpace.moduleCohomology Y.toRingedSpace 0).obj
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj F)))
      (d :
        (forget₂ (ModuleCat.{v} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{v}).obj
          ((RingedSpace.moduleCohomology Y.toRingedSpace 0).obj
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj F)) ⟶
        (forget₂ (ModuleCat.{v} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{v}).obj
          ((RingedSpace.moduleCohomology Y.toRingedSpace 2).obj
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj F))),
      (ComposableArrows.mk₄ (0 : (0 : AddCommGrpCat.{v}) ⟶ _)
        (Scheme.Modules.moduleCohomologyEdgeMap f F 1) c d).Exact ∧
      ∀ (_hzero : IsZero
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj F)),
        Nonempty ((
          (forget₂ (ModuleCat.{v} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
            AddCommGrpCat.{v}).obj
            ((RingedSpace.moduleCohomology Y.toRingedSpace 1).obj
              ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj F))) ≅
          (forget₂ (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
            AddCommGrpCat.{v}).obj ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj F)) := by
  sorry

end AlgebraicGeometry
