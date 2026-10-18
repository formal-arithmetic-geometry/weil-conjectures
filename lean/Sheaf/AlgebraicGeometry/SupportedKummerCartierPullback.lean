/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.AlgebraicGeometry.PicardTensorDualComparisonIso
import Sheaf.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Cartier line bundle and canonical section under Cartier-preserving pullback

Source: Stacks Project, Tag 0C4U, lemma-pullback-effective-Cartier-divisors
(blueprint: lem-asd-supported-kummer-cartier-pullback).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

variable {T T' : Scheme.{u}}

/-- Canonical dual comparison for the pullback of the structure sheaf, obtained from the
transpose-of-evaluation comparison.

Source: Stacks Project, Tags 0096 (pullback of the structure sheaf) and 0FNV/01C8
(base change for duals of finite locally free modules).
(blueprint: lem-asd-supported-kummer-cartier-pullback) -/
noncomputable def tensorPullbackUnitDualMap (h : T' ⟶ T) :
    (Modules.unit T')ᵛ ⟶ (Scheme.Modules.tensorPullback h).obj (Modules.unit T)ᵛ := by
  letI : IsIso (Modules.picardTensorDualComparison h (Modules.unit T)) :=
    AlgebraicGeometry.Scheme.picardTensorDualComparison_isIso h (Modules.unit T)
  exact Modules.dualMap (Scheme.Modules.tensorPullbackObjUnitToUnit h) ≫
    (asIso (Modules.picardTensorDualComparison h (Modules.unit T))).inv

/-- The Cartier line bundle and its canonical section pull back along a morphism whose
scheme-theoretic inverse-image ideal is again invertible.

The displayed dual-map equality is the canonical-section clause: the dual of the ideal inclusion
is preserved after the tensor pullback and the structure-sheaf identification. The proof follows
Stacks Tag 0C4U by local regular equations, the ideal-image base-change statement, and gluing;
all proof steps are recorded in the DAG node `lem-asd-supported-kummer-cartier-pullback`.
(blueprint: lem-asd-supported-kummer-cartier-pullback) -/
theorem exists_tensorPullback_dual_toModules_iso
    (h : T' ⟶ T) {J : T.IdealSheafData} (hJ : J.IsInvertible)
    (hJ' : (J.comap h).IsInvertible) :
    ∃ e : (Scheme.Modules.tensorPullback h).obj J.toModulesᵛ ≅ (J.comap h).toModulesᵛ,
      tensorPullbackUnitDualMap h ≫
          (Scheme.Modules.tensorPullback h).map (Modules.dualMap J.toModulesι) ≫ e.hom =
        Modules.dualMap (J.comap h).toModulesι := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
