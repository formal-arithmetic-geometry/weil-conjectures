/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.PointEquivariantDiagramData
/-! # Lifting a point diagram and its coefficient extensions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w vI
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Include an already realized diagram at its original common coefficient stage.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7,
and step 8 of lem-zl-point-equivariant-diagram-lift
(blueprint: lem-zl-point-equivariant-common-stage).

Proof: Apply the literal stage inclusion to G. The common-stage truncation formula
puts its objects in the heart. Whisker theta with inclusion and precompose with the
published stage-pullback comparison. Obtain eta by the specified stage-fibre
comparison followed by scalar-extended eta. Their components are exactly the first
two required equations. The normalized common-stage transport is the inclusion of
the original transport, including its canonical Shrink and tensor-tower comparisons.
It is therefore invertible and gives tOmega with the stated transport square.
Substitute this square and the component formulas to cancel the comparisons and
reduce the Frobenius and inverse equations to the original fibre formulas. All
relations and inverse equations hold at F before inclusion, without enlargement.
Exact scalar extension to Omega preserves the vector-space diagrams; reflection
by the common-stage point-heart equivalence gives short exactness, monomorphisms
and the cokernel universal properties. Its faithfulness also gives the relation
clause. Thus the prescribed stage and all canonical comparisons are retained. -/
theorem zl_point_equivariant_common_stage
    (F : Padic.FiniteCoefficientFields l Ω)
    {I : Type w} [Category.{vI} I]
    (V : I ⥤ ModuleCat.{u} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (A : ∀ i, V.obj i ≅ V.obj i)
    (G : I ⥤ sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (Spec (.of D.k)))
    (hG : ∀ i, sfRationalHeartProperty l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (Spec (.of D.k)) (G.obj i))
    (theta : G ⋙ zlDiagramPullback D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ≅ G)
    (eta : G ⋙ zlDiagramFiber D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ≅ V)
    (t : ∀ i, (zlDiagramFiber D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj (G.obj i) ≅
      (zlDiagramFiber D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj
        ((zlDiagramPullback D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj (G.obj i)))
    (hreal : ZlPointDiagramRealization D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) V A G hG theta eta t) :
    ZlCommonStageDiagram D l hl Ω F V A G theta eta t := by
  sorry

end WeilConjectures
