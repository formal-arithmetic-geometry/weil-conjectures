/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LocalRHomDefinitions
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement

/-! # Local RHom comparison and its cohomological lower bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-local-rhom-shift-sequence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC u w wSlice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules
namespace CategoryTheory.LocalRHom.Shifts

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))]


/-- The coherent shift sequence induced by the normalized target shift of internal Hom.
Source: Stacks Project, Tags 0A95 and 0147.
(blueprint: lem-per-local-rhom-shift-sequence). -/
@[instance_reducible]
def sequence (K : D.{uC, vC, u, w} J R) :
    (T.{uC, vC, u, w} J R K 0).ShiftSequence ℤ := by
  let : (RH.{uC, vC, u, w} J R K).CommShift ℤ :=
    RingedHomUniverses.homCommShift.{uC, vC, u, w} J R K
  infer_instance

/-- Comparison with the individual cohomology functors, normalized in degree zero.
Source: Stacks Project, Tag 0147.
(blueprint: lem-per-local-rhom-shift-sequence). -/
def comparison (K : D.{uC, vC, u, w} J R) (n : ℤ) :
    (sequence.{uC, vC, u, w} J R K).sequence n ≅ T.{uC, vC, u, w} J R K n :=
  if hn : n = 0 then by subst n; exact (sequence.{uC, vC, u, w} J R K).isoZero
  else Iso.refl _

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))] in
/-- The shift comparison is normalized at zero; internal Hom cohomology is homological.
Source: Stacks Project, Tags 0A95 and 0149.
(blueprint: lem-per-local-rhom-shift-sequence). -/
theorem properties (K : D.{uC, vC, u, w} J R) :
    comparison.{uC, vC, u, w} J R K 0 = (sequence.{uC, vC, u, w} J R K).isoZero ∧
      (∀ n : ℤ, (T.{uC, vC, u, w} J R K n).Additive) ∧
      (T.{uC, vC, u, w} J R K 0).IsHomological := by
  let : (RH.{uC, vC, u, w} J R K).CommShift ℤ :=
    RingedHomUniverses.homCommShift.{uC, vC, u, w} J R K
  have : (RH.{uC, vC, u, w} J R K).IsTriangulated :=
    RingedHomUniverses.hom_isTriangulated.{uC, vC, u, w} J R K
  exact ⟨by simp [comparison], fun n ↦ inferInstance, inferInstance⟩

end CategoryTheory.LocalRHom.Shifts
