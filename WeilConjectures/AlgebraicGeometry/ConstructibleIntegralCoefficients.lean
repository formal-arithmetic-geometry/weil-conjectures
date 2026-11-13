/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsForward
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

/-!
# Constructibility of torsion sheaves with integral coefficients

Source: Stacks Project, Tags 03RW and 095E; the comparison of (2) and (3)
for torsion sheaves and the canonical integral module structure.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A torsion abelian sheaf is constructible as an integral module sheaf exactly
when its underlying sheaf of sets is constructible.

Source: Stacks Project, Definition 03RW (2), (3), Lemma 095E, and the comparison
needed in the retract argument of Lemma 03SD. This comparison is written out here;
03RW does not identify the two notions for nontorsion sheaves. -/
theorem isConstructibleSheaf_integral_iff {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : X.IsTorsionAbelianSheaf F) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    IsConstructibleSheaf ((sheafCompose X.smallEtaleTopology E).obj F) ↔
      IsConstructibleEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) := by
  dsimp
  constructor
  · exact isConstructibleSheaf_integral_forward F hF
  · exact isConstructibleSheaf_integral_backward F hF

end AlgebraicGeometry.Scheme
