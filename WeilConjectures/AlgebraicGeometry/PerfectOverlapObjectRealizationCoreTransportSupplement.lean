/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapNestedSiteCompatibility
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalenceSupplement
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram
public import WeilConjectures.AlgebraicGeometry.PerfectHomComparisonTriangleSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory
attribute [local instance_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  TopCat.Hom.frameHom
attribute [local irreducible] perfectHomComposition
  openSiteReturnIso

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

private theorem cancel_iso_pasting {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (s : D ≅ B)
    (g : D ⟶ E) (h : E ⟶ D) (gh : g ≫ h = 𝟙 D) :
    f = 𝟙 A ≫ f ≫ s.inv ≫ g ≫ 𝟙 E ≫ h ≫ s.hom := by
  simp only [Category.id_comp, Category.comp_id,
    ← Category.assoc, gh, Category.comp_id, Iso.inv_hom_id]
section

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

set_option linter.unusedSectionVars false in
/-- The fixed local composite comparison has the prescribed composition formula.
Source: Stacks Project, Tag 0D5S. This is its defining composite, with the
restricted geometric equality kept as a proof rather than expanded by users.
(blueprint: def-pc-perfect-overlap-composite-transport-api). -/
theorem perfectOverlapCompositeLocalIso_eq
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (W : Y₀.Opens) :
    let hP : gf ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let hcomp : g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP ≫ (f ∣_ W) = gf ∣_ W := by
      apply (cancel_mono W.ι).1
      simp only [Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
    perfectOverlapCompositeLocalIso f g gf hgf W =
      perfectHomComposition _ _ ≪≫
    eqToIso (congrArg (fun a ↦ derivedPullback a) hcomp) := by
  intro hP hcomp
  rfl

set_option linter.unusedSectionVars false in
end

section
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Characterizing equation for the fixed local composite without requiring an
open-site derived-category instance.  The definition is in this module, so its
no-expose body may be unfolded here; downstream modules use this named equation.
-/
theorem perfectOverlapCompositeLocalIso_eq_compositionTo_global
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U : Y.Opens) :
    let hP : g ⁻¹ᵁ U ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let j := gk.resLE (f ⁻¹ᵁ U) (g ⁻¹ᵁ U) hP
    let hj : j ≫ (f ∣_ U) = g ∣_ U := by
      apply (cancel_mono U.ι).1
      simp only [Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
    perfectOverlapCompositeLocalIso f gk g hgf U =
      compositionTo j (f ∣_ U) (g ∣_ U) hj := by
  intro hP j hj
  unfold perfectOverlapCompositeLocalIso compositionTo
  rfl

end

end AlgebraicGeometry
