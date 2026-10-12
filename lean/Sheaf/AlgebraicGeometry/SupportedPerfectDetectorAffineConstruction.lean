/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

/-! # Affine Koszul construction with its open restriction unit
Source: Stacks Project, Tags 0A9A and 09IR.
(blueprint: lem-pc-supported-perfect-detector-affine-construction).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Construct the supported Koszul object and its orthogonality comparison with the open unit.
Source: Stacks Project, Tags 0A9A and 09IR.
(blueprint: lem-pc-supported-perfect-detector-affine-construction).

Proof:
1. Present X as Spec A. The quasi-compact complement U is covered by finitely many D(f_i).
   Sheafify and localize the finite Koszul complex on these functions to obtain E.
2. Finite free Koszul terms make E perfect and its homology quasi-coherent. Multiplication
   by each f_i is null-homotopic, so the homology stalks vanish on U (Tag 0663).
3. Exact restriction to U has a derived right adjoint R. Transport Tag 09IR along the
   affine presentation: for any quasi-coherent K orthogonal
   to all shifts of E, the canonical unit K to R(K restricted to U) is invertible.
   The empty tuple and the empty scheme satisfy the same assertion. -/
theorem supported_perfect_detector_affine_construction
    (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (hU : (U : Set X) = Tᶜ) :
    ∃ (E : schemeDerivedQCohCategory X)
      (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X)
      (adj : (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R),
      Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsIso (adj.unit.app K.obj) := by
  sorry

end AlgebraicGeometry
