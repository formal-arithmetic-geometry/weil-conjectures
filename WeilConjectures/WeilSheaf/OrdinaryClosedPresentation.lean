/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeExceptionalForgetful
public import WeilConjectures.AlgebraicGeometry.NativeWeilClosedForgetful

/-! # Closed structure under the closure and section presentation

Source: current blueprint, cor-coef-verdier-weil-equivariance, first-map paragraph;
native dual comparison proof step 3 (blueprint: lem-sf-ordinary-closed-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open WeilConjectures.AdicQbarRealization WeilConjectures.NativeExceptionalForgetful
open AlgebraicGeometry.ProEtaleWeilSheaf

namespace WeilConjectures.NativeDualPresentation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (R : Family l D) (X : Space D)

/-- Transport the specified ordinary closed model, retaining its evaluation transpose.
Source: current blueprint, cor-coef-verdier-weil-equivariance, first-map paragraph;
native dual comparison proof step 3 (blueprint: lem-sf-ordinary-closed-presentation).

Proof: the closure map is the base change of an algebraic-closure isomorphism.
Its direct image and the section-module presentation are exact equivalences of
module categories. Their pointwise tensor comparison identifies the two signed
total tensors on K-flat representatives. The ordinaryTensorModels normalization
of N identifies its tensor with that total tensor. Localizing these comparisons
gives t, natural in both variables. On K-injective representatives the same exact
equivalences preserve product-total sheaf Hom. The ordinaryModel and representative
fields identify N's ordinary Hom with that model. The componentwise uncurrying
normalization in ordinaryTensorModels identifies the resulting Hom arrow with the
transpose of t inverse followed by transported evaluation. Thus the Hom comparison
is invertible and has exactly the displayed normalization. Resolution independence
extends both comparisons to all derived arrows. This argument includes zero objects
and the empty scheme, where the same unit and counit identities still hold. -/
theorem ordinary_closed_presentation (N : NativeClosedComparison D.k₀ l X.base.left)
    (hN : N.Compatible) :
    let Q := (ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctor ⋙
      sectionDerived l (geometric D X).base.left (R.data (geometric D X)).realization
    letI := (R.data (geometric D X)).units
    let Z := (R.data (geometric D X)).tensor.closed
    ∃ t : N.ordinaryClosed.tensor ⋙ Q ≅ Q.prod Q ⋙ Z.tensor,
    ∃ h : N.homModels.ordinaryHom ⋙ Q ≅
        Q.op.prod Q ⋙
          ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization,
    ∀ A B, (h.app (op A, B)).hom = Z.transpose _ _ _
      ((t.app (N.homModels.ordinaryHom.obj (op A, B), A)).inv ≫
        Q.map (N.ordinaryClosed.evaluation A B)) := by sorry

end WeilConjectures.NativeDualPresentation
