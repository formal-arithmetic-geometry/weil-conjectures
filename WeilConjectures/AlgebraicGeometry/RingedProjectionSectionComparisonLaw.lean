/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedProjectionCoherenceData

/-! Field-level coherence law for normalized ringed projection tensor comparisons.
(blueprint: lem-sfb-ringed-projection-tensor-laws-section-comparison-law) -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence

/-- Section comparison law for normalized ringed projection tensor comparisons.
Source: Stacks Project, Tags 0D6D and 0FPI; section specialization.
The proof uses the normalized section representative square, the ordinary tensor
contraction identity, and descent from flat K-flat representatives.
(blueprint: lem-sfb-ringed-projection-tensor-laws-section-comparison-law) -/
theorem ringedProjectionSectionComparisonLaw
    (constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
      TensorConstraints X a) :
    ∀ {X W : RingedTensorCorner.{u, w}}
      (i : RingedTensorEdge W X) (p : RingedTensorEdge X W)
      (a : RingedTensorModel X) (b : RingedTensorModel W)
      (s : Section i p) (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived),
      s.Normalized l → ∀ E Q : X.mateDerived,
        i.left.map ((p.tensorComparison a b).hom.app (E, Q)) ≫
            (i.tensorComparison b a).hom.app (p.left.obj E, p.left.obj Q) ≫
            X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q)) =
          l.hom.app (X.tensor.obj (E, Q)) := by
  sorry

end SheafOfModules.ProjectionCoherence
