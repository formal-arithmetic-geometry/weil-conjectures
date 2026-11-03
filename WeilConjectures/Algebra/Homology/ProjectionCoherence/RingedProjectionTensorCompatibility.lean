/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionTensorConstraints
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionAssociativityLaw
import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionIdentityLaw
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareModuleTensorCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorTotalComponent
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorEdgeRepresentativeEquation
import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # Tensor compatibility in arbitrary representative presentations

Source: Stacks Project, Tags 06YS, 06YU, 07A4 and 0D6D.
-/

@[expose] public section

set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence

set_option linter.checkUnivs false in
/-- Tensor constraints and compatibility of already normalized pullback comparisons.
No comparison is constructed by this interface.
Source: Stacks 06YS, 06YU, 07A4 and 0D6D
(blueprint: lem-sfb-ringed-projection-tensor-compatibility). -/
structure TensorCompatibility where
  constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
    TensorConstraints X a
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

set_option linter.checkUnivs false in
end SheafOfModules.ProjectionCoherence
