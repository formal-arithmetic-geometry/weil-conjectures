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
import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicActualSourceTowerNormalized
import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicActualTargetTowerNormalized

/-! # Normalization of the actual source and exceptional coefficient systems -/

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

/-- The actual strict reduction and exceptional systems are normalized, with their
specified finite objects, transitions and evaluations.

Source: latest blueprint, smooth-purity transport coefficient-change proof (1),
`det-sp-tower-gamma` (3); original normalized-purity-lift node, proof steps 1--2.
(blueprint: lem-pur-adic-actual-systems-normalized).

Proof: use the coherent reduction construction for the integral source. Its quotient
balancing maps satisfy identity and composition; source finiteness makes every canonical
b^U invertible and identifies its transposed normalizations with the displayed source
transitions. Conjugate the quotient system by these isomorphisms, retaining its actual
restricted strict tower. For the target, retain integralExceptionalSystem itself.
The finite reductions of K have one lower cohomological bound and constructible etale
origin. The derived coefficient-site comparison transports their normalized system to
the etale side. The etale compact-support system right adjoint preserves normalization
and lower bounds and evaluates to the finite exceptional right adjoints with their
specified transition mates. Transport back and forget to completed coefficients.
Its evaluation comparisons are exactly purAdicExceptionalEvaluation by their counit
normalizations. Both constructions give the required Hom bijections, identity and
quotient cocycles, and the displayed equalities with the original strict towers.
This works also for zero K, equal indices and empty schemes: the unit, counit and
identity quotient constructions specialize without an extra nonemptiness assumption. -/
theorem actual_systems_normalized
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) :
    ∃ U V : NormalizedDVRTower C.l E X D C.different,
      U.tower = sourceTower D C E f d K ∧
      V.tower = targetTower D C E f K ∧
      (∀ n : ℕ,
        HEq (U.M n) (purAdicFiniteArrow D C E f d K hK n).left ∧
        HEq (V.M n) (purAdicFiniteArrow D C E f d K hK n).right ∧
        HEq (U.evaluationIso n).hom (sourceEvaluation D C E f d K hK n) ∧
        HEq (V.evaluationIso n).hom (targetEvaluation D C E f d K hK n).hom) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        HEq (U.tau h) (purAdicFiniteSourceTransition D C E f d K hK h) ∧
        HEq (V.tau h) (exceptionalTransition D C E f d K hK h)) := by
  obtain ⟨U, hUtower, hUeval, hUtau⟩ :=
    source_tower_normalized D C E f d K hK
  obtain ⟨V, hVtower, hVeval, hVtau⟩ :=
    target_tower_normalized D C E f d K hK
  refine ⟨U, V, hUtower, hVtower, ?_, ?_⟩
  · intro n
    exact ⟨hUeval n |>.1, hVeval n |>.1, hUeval n |>.2, hVeval n |>.2⟩
  · intro m n h
    exact ⟨hUtau h, hVtau h⟩

end WeilConjectures.AdicNormalizedPurity
