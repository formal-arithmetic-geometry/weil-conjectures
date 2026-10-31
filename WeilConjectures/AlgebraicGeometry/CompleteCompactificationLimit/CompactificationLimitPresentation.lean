/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport

/-! # Specializing the normalized coefficient reduction and total-limit adjunction
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-limit-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The fixed reduction and fixed total limit admit the finite tensor, counit and
unit-projection normalization, independently of geometric operations.
Source: blueprint direct-image proof, paragraph (2), reduction and quotient augmentation;
Stacks Project, Tags 0941 and 09T5.
(blueprint: lem-sp-compactification-limit-presentation).

Proof: use the actual ell-power ring diagram and its completed coefficient projections
in SequenceProjection.pushforwardLimitProjections. Its scalar forgetting is identified
with spCompletedStrictTower by the given coefficient equivalence and its transition
normalization, on sections. Exactness is also provided by the existing
spCompletedStrictTower exactness instances. The generic ordinary reduction has the
same finite tensor modules as ordinaryReduction: transport across r.coefficient,
then use the normalized scalar-model comparison. The equation for r.transition and
the generic tensor-section transition equation show these level maps form a strict
system isomorphism. Both left-derived functors are universal for these identified
ordinary functors, with r.counit transported to reductionCounit. Left-derived
uniqueness therefore gives the derived comparison preserving its counit. The generic
right adjoint is forgetting followed by the fixed-ring total limit. Right-derived
uniqueness identifies its limit functor with coefficientConstantTowerLimit, preserving
the resolution-normalized projections. Transport the generic adjunction by these
comparisons. At level n, identify ordinary reduction with the specified D.scalar model
by its local pure tensor formula. The scalar-model transpose equation and derived
uniqueness give evaluation and its equation with reductionCounit on every complex.
The generic unit-projection identity, under the projection-preserving right-adjoint
comparison and these normalized left-adjoint comparisons, is exactly unit_projection.
The ordinary comparison sends c tensor x to c tensor x, giving tensor_normalized.
All constructions take place on strict systems and unbounded complexes; neither
invertibility of ell on T nor boundedness nor constructibility is used. -/
theorem compactificationLimitPresentation (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D) :
    Nonempty (LimitPresentation l E T D r) := by sorry

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
