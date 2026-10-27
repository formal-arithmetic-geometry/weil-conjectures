/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteRestrictionCoefficientNormalization
public import Sheaf.Paper.FiniteRestrictionGeometricArrows

/-! # Integral assembly of finite coefficient restrictions

Source: Bhatt--Scholze 6.8.14, Remark 6.8.15; Stacks 0959, 03QP, 099N
(blueprint: lem-zl-finite-restriction-integral-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteRestrictionCoefficient
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage integralTransition transition stageSystem)
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Assembly of the integral part of finite coefficient restriction.

Source: Bhatt--Scholze 6.8.14, Remark 6.8.15; Stacks 0959, 03QP, 099N;
steps 1--4 of finite restriction coefficient descent
(blueprint: lem-zl-finite-restriction-integral-assembly).

Proof:
1. Apply finite completed-image comparison to f and its finite base change h.
Use integral pullback constructibility on y, v, h, each lift, and each point map.
These give the restricted functors on the fixed integral categories.
2. Restrict the completed tensor/pullback comparisons. Use strict direct-image
scalar comparison for both images, with its reconstruction and normalized scalar
comparisons. Finite-free completed scalar comparison identifies actual ring
extension, including ramified inclusions. No quotient exponents are identified.
3. On flat-term K-flat representatives the strict exchange is the completed
adjunction mate. The ordinary cochain adjunction, completion unit, and direct-image
reconstruction fix that adjunction. Composition and identity maps are those induced
by section pasting. Localization through good representatives therefore identifies
these maps with the strict-system arrows, yielding the endpoint isomorphisms and
ArrowsNormalized. The point target is the finite product of the individual point
pullbacks; its projections exhibit the limit. The empty product is zero.
4. Evaluate ordinary-adjunction scalar compatibility at the inverse adjunct of
identity. This is the completed counit square before reductions. Pull it along each
lift and use the normalized composition/unit comparisons. This proves each
restriction component square; finite product projections prove the tuple square.
The exchange square follows by taking mates. Identity extensions and successive
extensions give Laws and Coherent, with the specified balanced tensor associator.
5. The tower comparison is projection-normalized by finite completed-image
comparison, for both f and h. On strict systems scalar extension sends a tensor m
to a tensor the restriction of m; this is naturality of sheafified scalar extension
on pure tensors. This proves TensorRestrictionFormula without a nonempty-fibre
assumption. All endpoint comparisons use these same constructions. -/
theorem finiteRestrictionIntegralAssembly
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y) :
    ∃ (G : Geometry l Ω f y) (I : IntegralComparisons l f y Ω)
      (N : Endpoints l Ω f y G I) (J : GeometricArrows l Ω f y G),
      G.Normalized ∧ I.Laws ∧ I.Coherent ∧ N.ScalarNormalized ∧
      J.Normalized l Ω f y ∧ N.ArrowsNormalized l Ω f y J ∧
      TowerAgreement l Ω f ∧ TowerAgreement l Ω (pullback.snd f y) ∧
      TensorRestrictionFormula l Ω f y := by sorry

end WeilConjectures.FiniteRestrictionCoefficient
