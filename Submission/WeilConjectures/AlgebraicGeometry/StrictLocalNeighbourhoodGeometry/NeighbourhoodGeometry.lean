/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
public import Submission.WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical neighbourhood geometry on the small colimit model

Transport upstream's geometry along the canonical spectrum-colimit isomorphism.
Source: Stacks Project, Tag 03Q9, first proof paragraph.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- The canonical comparison of the two strict-local pullbacks, over X.
Source: Stacks Project, Tag 03Q9; final-functor colimit comparison.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport). -/
noncomputable def strictLocalSmallModelPullbackIso {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    pullback f (Scheme.strictHenselizationStructuralMap s) ≅
      pullback f (Scheme.strictLocalizationToBase s) :=
  asIso (pullback.map _ _ _ _ (𝟙 X)
    (Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv) (𝟙 S)
    (by simp) (by simpa using (Scheme.smallStrictHenselizationColimitIso_toBase s).symm))

namespace StrictLocalNeighbourhoodGeometry

/-- Upstream's legs expressed on the small coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport). -/
noncomputable def smallModelLegs {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s) :
    (Functor.const (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))).obj
      (pullback f (Scheme.strictHenselizationStructuralMap s)) ⟶
        strictLocalNeighbourhoodDiagram f s :=
  (Cone.mk _ Q.legs).extend (strictLocalSmallModelPullbackIso f s).hom |>.π

/-- The transported legs have the original projection to X.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport).
Proof: compose the upstream projection equation with the comparison and use the
first projection formula for the pullback map. -/
theorem smallModelOver {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Q.smallModelLegs.app i ≫ (strictLocalNeighbourhoodProjection f s).app i =
      pullback.fst f (Scheme.strictHenselizationStructuralMap s) := by
  change (strictLocalSmallModelPullbackIso f s).hom ≫ Q.legs.app i ≫ _ = _
  rw [Q.over]
  simp [strictLocalSmallModelPullbackIso]

end StrictLocalNeighbourhoodGeometry
end AlgebraicGeometry.Etale
