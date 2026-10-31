/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
/-! Field-level coherence law for normalized ringed projection tensor comparisons.
(blueprint: lem-sfb-ringed-projection-tensor-laws-composition-law) -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence
/-- Composition law for normalized ringed projection tensor comparisons.
Source: Stacks Project, Tags 0D6D and 0FPI; composition of normalized pullbacks.
(blueprint: lem-sfb-ringed-projection-tensor-laws-composition-law) -/
theorem ringedProjectionCompositionLaw
    (constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
      TensorConstraints X a) :
    ∀ {X Y Z : RingedTensorCorner.{u, w}}
      (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y)
      (h : RingedTensorEdge Z X) (a : RingedTensorModel X)
      (b : RingedTensorModel Y) (c : RingedTensorModel Z)
      (s : Composition f g h) (l : h.left ≅ g.left ⋙ f.left),
      s.Normalized l → ∀ E Q : Z.mateDerived,
        l.hom.app (Z.tensor.obj (E, Q)) ≫
            f.left.map ((g.tensorComparison c b).hom.app (E, Q)) ≫
            (f.tensorComparison b a).hom.app (g.left.obj E, g.left.obj Q) =
          (h.tensorComparison c a).hom.app (E, Q) ≫
            X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q)) := by
  sorry
end SheafOfModules.ProjectionCoherence
