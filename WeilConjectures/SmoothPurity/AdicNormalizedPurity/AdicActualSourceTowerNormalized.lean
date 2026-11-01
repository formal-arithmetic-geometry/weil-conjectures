/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicNormalizedPuritySystems
import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceFiniteness
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel

/-! # Normalized actual source tower for adic purity -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AdicNormalizedPurity

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The actual source reduction sequence has a normalized DVR tower with the prescribed
finite source objects, evaluations, and transitions.

Source: the first construction step of the actual normalized-systems proof in the
smooth-purity transport argument (blueprint: lem-pur-adic-actual-source-tower-normalized).
Proof: apply the coherent coefficient-sequence Roos model to the pullback reduction
calculus.  The calculus supplies normalization; the source finiteness reductions are
invertible and transport the model's finite evaluations and quotient cocycle to the
specified finite purity source presentations.  The defining evaluation and transition
composites are then the displayed `sourceEvaluation` and
`purAdicFiniteSourceTransition`, by the source reduction square and its cocycle. -/
theorem source_tower_normalized
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) :
    ∃ U : NormalizedDVRTower C.l E X D C.different,
      U.tower = sourceTower D C E f d K ∧
      (∀ n : ℕ,
        HEq (U.M n) (purAdicFiniteArrow D C E f d K hK n).left ∧
        HEq (U.evaluationIso n).hom (sourceEvaluation D C E f d K hK n)) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        HEq (U.tau h) (purAdicFiniteSourceTransition D C E f d K hK h)) := by
  sorry

end WeilConjectures.AdicNormalizedPurity
