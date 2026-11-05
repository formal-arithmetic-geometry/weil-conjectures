/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Bounded coherent cohomology of perfect complexes

Source: Stacks Project, Derived Categories of Schemes, Tag 0FXU, part (1).
(blueprint: lem-pc-perfect-noetherian-cohomology).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finitePresentation_overEquiv_inverse (X : Scheme.{u}) (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFinitePresentation] :
    ((Modules.overEquiv (X := X) U).inverse.obj M).IsFinitePresentation := by
  have (V : CategoryTheory.Over U) :
      (Over.post (X := V) U.overEquivalence.symm.inverse).IsContinuous
        ((Opens.grothendieckTopology ↥X).over U |>.over V)
        ((Opens.grothendieckTopology ↥U).over
          (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  exact @SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ M _

end AlgebraicGeometry.Scheme
