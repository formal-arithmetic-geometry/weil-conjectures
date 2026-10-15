/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle

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
  unfold perfectOverlapCompositeLocalIso compositionTo
  rfl

end AlgebraicGeometry
