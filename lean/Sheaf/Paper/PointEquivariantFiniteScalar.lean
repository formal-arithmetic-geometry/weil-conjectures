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
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- A realized point Weil diagram extends along any finite coefficient embedding.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7,
and step 7 of lem-zl-point-equivariant-diagram-lift
(blueprint: lem-zl-point-equivariant-finite-scalar).

Proof: Extend G by the recorded rational scalar functor. Truncation compatibility
puts every extended object in the heart. Whisker theta with scalar extension and
precompose with the inverse normalized pullback/scalar comparison. Whisker eta
with module scalar extension and precompose with the specified point-fibre/H^0
comparison. These are natural isomorphisms, with exactly the component equations
in the conclusion. The scalar naturality of point transport identifies its extended
component with the conjugate of scalar-extended t; this gives an isomorphism tL
and the displayed transport square. Substitute this square and the two component
equations into the original forward and inverse fibre formulas. Functoriality and
cancellation prove the new formulas and local Frobenius equation. Exact field
extension preserves the vector-space exact diagrams, and the exact point-heart
equivalence reflects their short exactness, monomorphisms and cokernel universal
properties. Faithfulness and the natural fibre comparison reflect all parallel-arrow
relations. These arguments also cover the zero diagram and arbitrary invertible A. -/
theorem zl_point_equivariant_finite_scalar
    {I : Type w} [Category.{vI} I]
    (V : I ⥤ ModuleCat.{u} E) (A : ∀ i, V.obj i ≅ V.obj i)
    (G : I ⥤ sfRationalConstructibleCategory l E (Spec (.of D.k)))
    (hG : ∀ i, sfRationalHeartProperty l E (Spec (.of D.k)) (G.obj i))
    (theta : G ⋙ zlDiagramPullback D l hl E ≅ G)
    (eta : G ⋙ zlDiagramFiber D l hl E ≅ V)
    (t : ∀ i, (zlDiagramFiber D l hl E).obj (G.obj i) ≅
      (zlDiagramFiber D l hl E).obj ((zlDiagramPullback D l hl E).obj (G.obj i)))
    (hreal : ZlPointDiagramRealization D l hl E V A G hG theta eta t) :
    ZlFiniteScalarDiagram D l hl E L ι V A G theta eta t := by
  sorry

end WeilConjectures
