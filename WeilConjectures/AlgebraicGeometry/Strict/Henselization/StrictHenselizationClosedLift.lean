/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-!
# The distinguished geometric closed point lies over the original point

Source: Stacks Project, Tag 04HX.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The coordinate-ring evaluation gives the canonical closed-point lift over `s`.
Source: Stacks Project, Tag 04HX. -/
theorem strictHenselizationClosedLift_over
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s)) ≫
      strictHenselizationStructuralMap s = s := by
  have := (strictHenselization_properties s).2.1
  obtain ⟨j⟩ := IsCofiltered.nonempty
    (C := SmallModel.{u} (strictHenselizationNeighbourhoods s))
  have hstruct := (exists_strictHenselizationStructuralMap s).choose_spec j
  change _ = strictHenselizationStructuralMap s at hstruct
  rw [← hstruct]
  rw [← Scheme.isoSpec_Spec_inv]
  simpa only [Category.assoc] using!
    (congrArg (fun f ↦ f ≫ ((AffineEtale.Spec S).obj
      ((equivSmallModel.{u}
        (strictHenselizationNeighbourhoods s)).inverse.obj j).1).hom)
      (strictHenselizationRingPointEvaluation_pointed s j)).trans
        (Over.w ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).2)

end AlgebraicGeometry.Scheme
