/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOperationIdentificationSpecification

/-! # Core operation data for common-stage smooth operations

Source: smooth-purity transport, Step 2, operation and transport construction
(blueprint: lem-pur-common-stage-smooth-operation-core).

This intermediate statement isolates the operation witnesses, their comparison
isomorphisms, representative formulas, and compatible transformation transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CommonStageSmoothOperationIdentification

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System.{u, v} l Ω D hl (f := f))
  [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (JX : FdCoefficientComparison l Ω X) (JY : FdCoefficientComparison l Ω Y)

/-- The operation witnesses and all common-stage transport equations.
Source: smooth-purity transport Step 2, operation and transformation paragraphs
(blueprint: lem-pur-common-stage-smooth-operation-identification).
The proof constructs the two coherent exact stage morphisms from the finite
operation comparisons, applies the generic descent formulas, and transports the
framework representatives through the coefficient equivalences. -/
theorem commonStageSmoothOperationCore :
    ∃ (H G : StageSystem.CoherentExactMorphism
        (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out))
      (RH : commonOperation.{u, v} l Ω D hl f d S false ⋙ JX.equivalence.functor ≅
        JY.equivalence.functor ⋙ H.base.functor)
      (RG : commonOperation.{u, v} l Ω D hl f d S true ⋙ JX.equivalence.functor ≅
        JY.equivalence.functor ⋙ G.base.functor),
      OperationSpec l Ω D hl f d S JX JY false H.base RH ∧
      OperationSpec l Ω D hl f d S JX JY true G.base RG ∧
      FrameworkRepresentativeSpec l Ω X JX ∧
      FrameworkRepresentativeSpec l Ω Y JY ∧
      TransformationSpec H.base G.base ∧
      TransportSpec l Ω D hl f d S JX JY H G RH RG := by
  sorry

end WeilConjectures.CommonStageSmoothOperationIdentification
