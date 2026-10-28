/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.SfIntegralReductionTower

/-! # Tensoring the restricted quotient tower

Source: Stacks Project, Tags 03CZ, 06YY and 07A4; the coefficient-unit calculation in
`thm-coef-integral-verdier.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The canonical map from tensor with a restricted reduction to reduction of tensor.
It is constructed by the scalar adjunction, the normalized tensor comparison and its
inverse; no Hom object or dualizing complex occurs.
Source: Stacks 03CZ, 06YY and 07A4
(blueprint: lem-sf-integral-tensor-restriction-transition). -/
def restrictionTensor
    {a : TensorPresentation.{u, u} X (completedIntegralCommRingSheaf l E X D hl)}
    {n : ℕ} (m : ReductionPresentation l E X D hl a n)
    (K V : DerivedCategory (scalarReductionSource l E X)) :
    a.tensor.obj (K, (sfDerivedReductionRestricted l E X n).obj V) ⟶
      (sfDerivedReductionRestricted l E X n).obj (a.tensor.obj (K, V)) :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _
    (m.mu.hom.app (K, (sfDerivedReductionRestricted l E X n).obj V) ≫
      m.target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K))
          ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.counit.app
            ((scalarReductionDerivedExtension l E X n).obj V))) ≫ m.mu.inv.app (K, V))

/-- Tensoring the second input commutes with the consecutive quotient transition.

Source: Stacks 03CZ, 06YY and 07A4; coefficient units and quotient maps in the first
paragraph of the integral Verdier proof.

Proof: choose K-flat complexes P and Q representing K and V and a K-flat resolution
of the restricted finite reduction of Q. Apply the scalar adjunction to the displayed
map. Its counit multiplies the scalar factor and its tensor comparisons are fixed by
ReductionPresentation.normalization. Consequently, on a homogeneous tensor it is
x tensor (b tensor y) maps to b tensor (x tensor y), with b in degree zero. The two
routes across the consecutive quotient square therefore both send this tensor to
q(b) tensor (x tensor y), where q is the actual quotient map. Balanced pure tensors
generate the ordinary sheafified tensors, and the total tensor is a direct sum in
each degree, so these formulas give equality of chain maps. The representative
normalization of sfDerivedReductionTransition identifies these maps with the stated
transitions. Localize the equality and cancel the K-flat resolution and comparison
isomorphisms. This works in every degree and at n = 0 without boundedness or
constructibility assumptions.
(blueprint: lem-sf-integral-tensor-restriction-transition). -/
theorem restrictionTensor_transition
    (a : TensorPresentation.{u, u} X (completedIntegralCommRingSheaf l E X D hl))
    (m : ∀ n : ℕ, ReductionPresentation l E X D hl a n)
    (K V : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    a.tensor.map (Prod.mkHom (𝟙 K) ((sfDerivedReductionTransition l E X n).app V)) ≫
        restrictionTensor l E X D hl (m n) K V =
      restrictionTensor l E X D hl (m (n + 1)) K V ≫
        (sfDerivedReductionTransition l E X n).app (a.tensor.obj (K, V)) := by
  sorry

end WeilConjectures.IntegralHom
