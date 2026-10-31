/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicNormalizedPuritySystems
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel

/-! # Normalized actual exceptional tower for adic purity -/

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

/-- The actual exceptional coefficient sequence has a normalized DVR tower with the
prescribed finite exceptional objects, evaluations, and transitions.

Source: the second construction step of the actual normalized-systems proof in the
smooth-purity transport argument (blueprint: lem-pur-adic-actual-target-tower-normalized).
Proof: retain `integralExceptionalSystem` and apply the derived coefficient-site
comparison to its constructible finite reductions.  The pro-etale origin witnesses
supply the comparison hypotheses, while the strict etale exceptional adjoint preserves
normalization and identifies evaluations and transition mates.  Exact restriction to
completed coefficients gives the displayed `targetEvaluation` and
`exceptionalTransition`, with the finite endpoints identified by heterogeneous equality. -/
theorem target_tower_normalized
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) :
    ∃ V : NormalizedDVRTower C.l E X D C.different,
      V.tower = targetTower D C E f K ∧
      (∀ n : ℕ,
        HEq (V.M n) (purAdicFiniteArrow D C E f d K hK n).right ∧
        HEq (V.evaluationIso n).hom (targetEvaluation D C E f d K hK n).hom) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        HEq (V.tau h) (exceptionalTransition D C E f d K hK h)) := by
  sorry

end WeilConjectures.AdicNormalizedPurity
