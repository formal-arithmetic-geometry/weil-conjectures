/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenSquareComparison

/-! # The restricted composite uses the fixed pullback comparison -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The local comparison for a composite map is exactly the fixed
`compositionTo` at the restricted scheme maps. Source: Stacks Project,
Tag 0D5S. Both constructors use the same pinned composition family; the
only difference is the proof of the equality of restricted scheme maps,
which is irrelevant. -/
theorem perfectOverlapCompositeLocalIso_eq_compositionTo
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U : Y.Opens) :
    let hP : g ⁻¹ᵁ U ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let j := gk.resLE (f ⁻¹ᵁ U) (g ⁻¹ᵁ U) hP
    let hj : j ≫ (f ∣_ U) = g ∣_ U :=
      perfectOverlapRestrictedComposite f gk g hgf U
    perfectOverlapCompositeLocalIso f gk g hgf U =
      compositionTo j (f ∣_ U) (g ∣_ U) hj := by
  intro hP j hj
  rw [perfectOverlapCompositeLocalIso_eq f gk g hgf U]
  unfold compositionTo
  rfl

set_option linter.unusedSectionVars false in
/-- A pinned square comparison is the forward fixed comparison for one path
followed by the inverse comparison for the other. Source: Stacks Project,
Tag 0D5S. Expand both definitions and use the component equation of the
equality transport. -/
theorem singleComplexOpenSquareComparison_app_eq_compositionTo
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (M : schemeDerivedCategory S) :
    (singleComplexOpenSquareComparison f f' g g' h).app M =
      (compositionTo f' g (g' ≫ f) h.symm).hom.app M ≫
        (compositionTo g' f (g' ≫ f) rfl).inv.app M := by
  simp only [singleComplexOpenSquareComparison, compositionTo,
    NatTrans.comp_app, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.assoc, singleComplexOpenPinnedComposition,
    perfectHomComposition]

end AlgebraicGeometry
