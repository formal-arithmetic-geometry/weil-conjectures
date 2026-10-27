## What changed

Proved the assigned theorem by preparing the actual tensor/pullback finite-Tor input, factoring both the projection and the specified support comparison into their proper/open factors, and pasting the proper and open coefficient squares. The proof also assembles naturality, the two coefficient-composition equations and the two identity equations explicitly. The statement of concreteProjectionReductionSquare is unchanged.

Moved its existing data declarations to ConcreteProjectionReductionData, publicly reexported by the item, to avoid a cycle between the theorem and its component statements. The mathematical values are unchanged; supportComparison is fixed to its original arrow by a proved unique equality specification and supportComparison_eq, preventing expensive kernel reduction; coefficients and coefficientChange expose their constant-ring projections by reducibility attributes. ConcreteProjectionFactorizationData names the existing proper/open functors and their specified maps. ConcreteProjectionCoefficientCoherence proves the tensor, support and input composition and identity equations using normalized representative comparisons, scalar-adjunction uniqueness and the existing proper/open support cocycles.

Generalized ScalarPullbackCoefficientCoherence by removing the unnecessary IsOpenImmersion assumption on its two scalar/pullback clauses. Neither clause uses open extension. The existing theorem remains the named proof dependency with its original hole. All five existing consumers were checked unchanged against the generalized interface. Change records are coord/changes/D7-concrete-projection-data.md and coord/changes/D7-scalar-pullback-coefficient-coherence.md.

Repaired scalarId in OpenScalarTensorData to preserve its exact canonical value behind a proved unique equality specification, with scalarId_eq as its explicit API. This prevents kernel reduction through the derived localization when using the identity cocycle. The added data-selection theorem is proved and determines the isomorphism exactly. The repair is recorded in coord/changes/D7-scalar-identity-reduction.md.

## Proved and sorry left

Closed the original hole WeilConjectures.ConcreteProjectionReduction.concreteProjectionReductionSquare by a complete assembly from the component statements. This is a decomposition, not a net proof of all its mathematics: one original hole closed and two component holes added. The proper component proper_scalar_tensor_square is proved using the existing scalar counit square, scalar/pullback tensor coherence, and abstract mate calculation.

The added holes, each in its own module with a complete source argument and its own node, are:

- WeilConjectures.ConcreteProjectionReduction.open_scalar_tensor_square: lem-sf-concrete-open-scalar-tensor-square. The open tensor/scalar identity including the compactification pullback compositor.
- WeilConjectures.ConcreteProjectionReduction.supportComparison_quotient_isIso: lem-sf-concrete-support-scalar-isomorphism. Invertibility of the specified compact-support scalar mate on the finite-Tor constructible domain.

The copied existing AlgebraicGeometry.ProEtale.OpenScalarTensor.scalar_pullback_coefficient_coherence hole is retained, not added (lem-sp-open-scalar-coefficient-coherence). No definition contains a hole. The added scalarId_existsUnique and scalarId_eq theorems are proved and introduce no holes. In namespace WeilConjectures.ConcreteProjectionReduction, tensor_comp, tensor_id, support_comp, support_id, input_comp and input_id have complete proof bodies, as do the private adjunction-transport and square-pasting calculations. There are zero holes in the item or proper component, two new holes in its component modules, and one retained hole in the repaired interface module.

## No longer needed

Removed unused proof imports from the item: EtaleCompactSupportCoefficientChange, RingedTopoiCanonicalTensorPullbackOfUniverses, KFlatScalarComparisonNormalization, ProEtaleScalarMateNormalization, OpenScalarTensorNormalization, CompactSupportIntrinsicTensorComparison, IntrinsicCompactSupportRestriction, SuccessiveDerivedQuotientNormalization, and RingedCoefficientProjectionCocycle. Their mathematical coordinate identifications or component arguments are retained where needed in the three component nodes; their statements are not imported as unsupported specializations.

The new coherence module also removes the unused AdjunctionEvaluationComposition proof import (lem-pur-adjunction-evaluation-composition); the explicit uniqueness calculation only needs NormalizedAdjunctionComposition. The direct coefficient-composition argument uses normalized scalar tensor coherence and scalar-adjunction uniqueness, so it does not use lem-sfb-successive-derived-quotient-normalization or lem-pur-ringed-coefficient-projection-cocycle. The corresponding top-level tool approvals are removed. No adopted WeilConjectures declaration is removed, and no module is withdrawn. The unit route through the concrete reduction square is retained.

## Where the brief, the DAG or earlier work was wrong

The dependencies describe the correct mathematical argument, but several interfaces cannot be specialized as directly as the original plan suggests. RingedTensorCorner fixes the object and morphism universes of a site equal, whereas the project's pro-etale sites have objects in u+1 and morphisms in u. Its packaged statement cannot directly accept this site; the universe-polymorphic tensor_mate_coherence calculation inside the same module does apply and proves the proper component. OpenScalarTensorNormalization supplies an existentially selected model and choices; the assigned statement quantifies over every normalized model and choices. Its existential cannot supply the needed square for those arbitrary parameters. The stated scalar/pullback coefficient coherence also unnecessarily required an open immersion, although the argument uses the arbitrary morphism f. The interface repair removes that assumption and preserves all old consumers.

The compact-support finite coefficient theorem uses intrinsic constant-module coordinates. The assigned comparison uses the separately derived ringed proper/open coordinates. One must identify the normalized comparisons, not infer invertibility merely from isomorphic endpoints. The remaining support component explicitly retains this requirement and does not assume separated structure morphisms.

## New nodes

- def-sf-concrete-projection-reduction-data attaches the existing eighteen data declarations in their reexported module. Its definitions are the original ones.
- def-sf-concrete-projection-factors names the actual proper/open factors, the counit-defined proper projection and the open tensor map including its geometric compositor.
- lem-sf-concrete-projection-coefficient-coherence records the six proved tensor, support and input composition/identity equations.
- lem-sf-concrete-proper-scalar-tensor-square isolates the proper counit/tensor compatibility calculation; it asserts no projection isomorphism.
- lem-sf-concrete-open-scalar-tensor-square isolates the open tensor square and geometric pullback-composition compatibility.
- lem-sf-concrete-support-scalar-isomorphism isolates invertibility of the actual quotient coefficient comparison on finite-Tor constructible inputs.

Change records: coord/changes/D7-concrete-projection-data.md, coord/changes/D7-scalar-pullback-coefficient-coherence.md, and coord/changes/D7-scalar-identity-reduction.md.

## Forced adaptations

None. The delivered edit of Sheaf.Paper.IntegralCompactSupportCoefficientComparison (held by F8; new
transportedIdentity API and a restated comparison_identity) was not forced and had no change record;
the reviewer reverted it. ConcreteProjectionCoefficientCoherence now defines the transported identity
privately and restates comparison_identity locally (rewrite by its defining equation), so the
published comparison_identity is used unchanged.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
