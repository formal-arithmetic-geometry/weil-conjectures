/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionAssociativityLaw
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionIdentityLaw
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCompositionLaw
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionSectionComparisonLaw

/-! Compatibility laws for normalized ringed projection tensor comparisons.
(blueprint: lem-sfb-ringed-projection-tensor-laws)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence

set_option linter.checkUnivs false in
/-- The four coherence laws hold for any normalized family of tensor constraints.
Source: Stacks 06YS, 06YU, 07A4, 0D6D and 0FPI.
The proof descends each law to flat K-flat representatives, uses the ordinary
cochain tensor pullback equations there, and extends the resulting natural
transformations by localization. It is independent of constructing the constraints.
(blueprint: lem-sfb-ringed-projection-tensor-laws). -/
structure TensorCompatibilityLaws
    (constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
      TensorConstraints X a) where
  associativity : ∀ {X Y : RingedTensorCorner.{u, w}} (f : RingedTensorEdge Y X)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (E Q N : Y.mateDerived),
    f.left.map ((constraints Y b).associator E Q N).inv ≫
        (f.tensorComparison b a).hom.app (Y.tensor.obj (E, Q), N) ≫
        X.tensor.map (Prod.mkHom ((f.tensorComparison b a).hom.app (E, Q))
          (𝟙 (f.left.obj N))) =
      (f.tensorComparison b a).hom.app (E, Y.tensor.obj (Q, N)) ≫
        X.tensor.map (Prod.mkHom (𝟙 (f.left.obj E))
          ((f.tensorComparison b a).hom.app (Q, N))) ≫
        ((constraints X a).associator (f.left.obj E) (f.left.obj Q) (f.left.obj N)).inv
  identity : ∀ {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X)
    (a : RingedTensorModel X) (s : Identity h) (l : h.left ≅ 𝟭 X.mateDerived),
    s.Normalized l → ∀ E Q : X.mateDerived,
        (h.tensorComparison a a).hom.app (E, Q) ≫
          X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q)) =
        l.hom.app (X.tensor.obj (E, Q))
  composition : ∀ {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y) (h : RingedTensorEdge Z X)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (c : RingedTensorModel Z)
    (s : Composition f g h) (l : h.left ≅ g.left ⋙ f.left),
    s.Normalized l → ∀ E Q : Z.mateDerived,
        l.hom.app (Z.tensor.obj (E, Q)) ≫
            f.left.map ((g.tensorComparison c b).hom.app (E, Q)) ≫
            (f.tensorComparison b a).hom.app (g.left.obj E, g.left.obj Q) =
          (h.tensorComparison c a).hom.app (E, Q) ≫
            X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q))
  sectionComparison : ∀ {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W)
    (a : RingedTensorModel X) (b : RingedTensorModel W) (s : Section i p)
    (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived),
    s.Normalized l → ∀ E Q : X.mateDerived,
        i.left.map ((p.tensorComparison a b).hom.app (E, Q)) ≫
            (i.tensorComparison b a).hom.app (p.left.obj E, p.left.obj Q) ≫
            X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q)) =
          l.hom.app (X.tensor.obj (E, Q))

/-- The four displayed compatibility laws are obtained independently.
The proof restricts each law to flat K-flat representatives, applies the
ordinary cochain pullback tensor equations, descends the equalities through
the localization, and transports them through the chosen constraints.
Source: Stacks 06YS, 06YU, 07A4, 0D6D and 0FPI.
(blueprint: lem-sfb-ringed-projection-tensor-laws). -/
theorem ringedProjectionTensorLaws
    (constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
      TensorConstraints X a) : Nonempty (TensorCompatibilityLaws constraints) := by
  refine ⟨{ associativity := ?_, identity := ?_, composition := ?_, sectionComparison := ?_ }⟩
  · exact ringedProjectionAssociativityLaw constraints
  · exact ringedProjectionIdentityLaw constraints
  · exact ringedProjectionCompositionLaw constraints
  · exact ringedProjectionSectionComparisonLaw constraints

end SheafOfModules.ProjectionCoherence
