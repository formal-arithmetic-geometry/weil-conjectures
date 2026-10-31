/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictFiniteProjectionTensorData
import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictFiniteProjectionWordCompatibility

/-! Finite projection-word normalization in fixed scalar coordinates. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite tensor and projection word can be normalized in fixed coordinates.
Source: blueprint operations proof (2), finite tensor realization and projection.
(blueprint: new-lem-sp-strict-finite-projection-word).

Proof: equip sfIntrinsicModuleEquivalence with comparisonFiniteUnderlying.
The latter is the sheafification counit; use the inverse sheafification unit's
constant-scalar linearity and the counit triangle identity to prove its scalar
condition. Thus its equivalence and underlying comparison are exactly the two
prescribed fields, rather than arbitrary choices of a finite realization.

Restrict the levelTensorModels comparison to flat-term K-flat pairs. The native
and independent-coefficient K-flat predicates agree. Retain levelClosed.tensor
as the functor, and use the localization universal property on resolving pairs
to obtain TensorModel.descent. The representative comparison is the restriction
of the given one, so ComparisonFiniteTensorRepresentative follows by proof
irrelevance. Apply finite_tensor_total_comparison_exists to the prescribed
realization, then finite_tensor_derived_comparison_exists to that pure-summand
comparison and this tensor model. Their equations give FiniteTensorPin for the
same derived tensor comparison. Choose these comparisons for all T,n; the
specified equivalence, underlying comparison, functor, representative and pin
clauses are retained with their HEq identifications.

Compare the geometric tensor pullback maps on resolving pairs: the total tensor
pin and the normalized tensor pullback send every pure bidegree summand to the
same pure tensor. The sheaf tensor and direct-sum universal properties extend
this equality to signed total complexes, with the same differential signs;
localization extends it to derived pairs. The unit and counit equations of
coordinates transport the proper projection transpose through this square.
For the open factor, transpose the conjugated inverse published open tensor
map. Its transpose is the tensor of the open unit followed by the inverse tensor
pullback comparison. The ordinary open scalar square preserves that unit, and
its exact localization does too. Therefore levels.openTensor_mate identifies
the transposes, and injectivity of the open adjunction Hom equivalence identifies
the inverse maps. Cancel their isomorphisms to identify the forward open maps.
The compactification open is quasi-compact: c.i followed by the separated proper
map c.g is the quasi-compact f.

Finally expand the published compactification projection into the proper
projection, pushforward of the open tensor map and the final pullback compositor.
The compositor is transported by cancellation of the scalar equivalence unit
and counit in comparisonFiniteOrdinaryPull, then exact localization. Paste the
three transported squares and reassociate. This proves the final equality for
the same chosen tensor family. The argument covers arbitrary K,L, including
zero objects, identity open/proper factors and empty schemes. -/
theorem strictFiniteProjectionComparisonsExistence (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    (coordinates : StrictFiniteCoordinates l E b) :
    StrictFiniteProjectionComparisons l E b o levels coordinates := by
  obtain ⟨tensor, hdata⟩ := strictFiniteProjectionTensorData l E b
  exact ⟨tensor, hdata,
    strictFiniteProjectionWordCompatibility l E b o levels coordinates tensor hdata⟩

end AlgebraicGeometry.ProEtale.SpTowerShriek
