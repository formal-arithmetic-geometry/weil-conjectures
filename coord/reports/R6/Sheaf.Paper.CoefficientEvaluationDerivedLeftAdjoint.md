## What changed

Rebased the delivered R6 proof onto the current `sheaf-dag` target. The current target file is preserved as the source of the repair, while the reviewed R6 support modules and assembly proof are restored in the sandbox. All sandbox modules compile against the current baseline.

Reorganized the original item's support declarations into
`Sheaf.Paper.CoefficientEvaluationModels`, publicly re-exported by the item. Their mathematical
contents and the original theorem's signature are preserved. The change record documents this
interface relocation, with the downstream users.
No `WeilConjectures` source declaration, target signature, unit route or existing definition's
mathematical meaning is changed.

Constructed the strict extension adjunction and its normalized Hom formula from the existing
strict-system theory. Proved a general resolving-class derived-adjunction theorem retaining the
normalized transpose on all complex representatives, with independent localization universes.
Applied it to the actual coefficient tensors and evaluation extensions. Proved exact evaluation
detects quasi-isomorphisms, the zero formula above the extension level, the universal tensor
comparison below it, and descent of strict transitions with their localization equation.
Constructed sigma as an adjunction mate and proved its Hom formula for every derived morphism.
Constructed the normalized ordinary tensor comparisons, strict truncation maps and termwise
complex lifts, and derived the tensor unit by uniqueness of universal derived functors.

The original theorem assembles these constructions and the separate derived index-coherence
lemma into its original package. The remaining lemma concerns representative compatibility and
index composition, not existence of the evaluation or scalar adjunctions.

## Proved and sorry left

Original hole closed: `SheafOfModules.coefficientEvaluationDerivedLeftAdjoint` (one of one). The repair also restores the reviewed proofs of `SheafOfModules.coefficientSystem_abelian_exists` and `SheafOfModules.coefficientEvaluation_exact` that were present in the delivered R6 support interface.
The original item module contains zero `sorry` occurrences. The support module restores the reviewed proofs of `coefficientSystem_abelian_exists` and `coefficientEvaluation_exact`. One `sorry` remains in the deliberately split theorem `coefficientEvaluationDerivedCoherence` in `Sheaf.Paper.CoefficientEvaluationDerivedExtension`.

New hole: `SheafOfModules.coefficientEvaluationDerivedCoherence`, node
`lem-pur-coefficient-evaluation-derived-extension-coherence`, in
`Sheaf.Paper.CoefficientEvaluationDerivedExtension`. Its five conclusions are the sigma
representative equation, the derived tensor associator with its representative equation, and
the identity and composition laws for sigma. Its hypotheses supply the separately constructed
ordinary and derived adjunctions, normalized transitions and strict complex maps. The natural
language proof in its docstring explains the two transposes, K-flat comparison and strict
composition calculation. Its comparison equations determine the derived associator uniquely;
no arbitrary object is chosen from an existence statement.

This is a decomposition: one original hole closed and one strictly smaller hole added, net zero
holes in the delivered declarations; the ledger separately measures transitive closure changes.
The other new modules contain no sorry. In particular the named theorems proved are
`coefficientOrdinaryEvaluationExtension`, `Adjunction.exists_leftDerived_adjunction`,
`coefficientScalarDerivedAdjunction`, `coefficientEvaluationDerivedCore`,
`coefficientEvaluationDerivedAbove`, `coefficientEvaluationDerivedBelow`,
`coefficientEvaluationDerivedTransition`, `Adjunction.compositeMate_homEquiv`,
`coefficientTensorOrdinaryCoherence`, `coefficientEvaluationStrictSigma`,
`coefficientEvaluationOrdinaryCoherence`, and `coefficientTensorDerivedUnit`.

## No longer needed

Removed the following original proof-only imports from the relocated support interface:

- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Paper.PbcCompletedPullbackActual` (present again in the current target after the batch take-out; unused)

The resolving-class existence, saturation and essential-constancy results remain dependencies
of the general normalized adjunction proof; removing them from Models does not prune them
from the transitive proof closure. The Kan bridge remains used through resolving-class
existence. The independent-coefficient K-flat preservation argument remains in the index
coherence plan. The public imports of the old support interface are all retained.

The separate `lem-weil-pbc-exact-functor-derived-functor` and
`lem-weil-pbc-exact-functor-derived-factorization` wrappers are replaced by Mathlib's exact
`mapDerivedCategory` API. `lem-pc-pre-derived-adjoint-functors-general` is replaced by the
normalized compatibility theorem already available in
`Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`, which also handles all
representatives and the two chosen localization universes. The original generic derived
adjunction interface remains publicly available, but the new proof uses this normalized theorem
instead of invoking `lem-pc-derived-adjoint-functors` separately. The additional tensor-universe
and module pullback/pushforward proof imports are unnecessary for the fixed coefficient
construction. No existing module or declaration is withdrawn, and no source-library dependency
is claimed globally unused merely because this proof no longer imports it directly.

## Where the brief, the DAG or earlier work was wrong

The original single sorry combined several independently reusable results. The landing failure was caused by the target file moving after the delivery base; this packet takes the current target as its base and reapplies the reviewed proof. Existing generic
interfaces did not by themselves give the representative-normalized transpose with the chosen
cochain localization factors. The new resolving-class lemma supplies that glue rather than
postulating another copy of the full coefficient package. Its representative transpose holds
on every complex, stronger than the resolving-class computation needed here.

The regularity and adic-completeness assumptions are unnecessary for constructing these
adjunctions of unrestricted strict systems. They remain verbatim in the item's signature. The unused-variable linter is disabled only
for this theorem, with a comment explaining why its original regularity binder stays.
No quotient-ring flatness is used. Zero rings, ell equal to zero, repeated indices, and the
boundary between the tensor and zero components do not require extra assumptions.

The original interface-location change is recorded in
`coord/changes/R6-coefficient-evaluation-models.md`. There are no forced adaptations of another
group's modules. The unchanged finite-adjunction consumer compiles against the new interface.
The other direct consumer, `CoefficientSystemDerivedComparison`, times out both against the
published interface and against this sandbox; this is a pre-existing consumer limitation.

## New nodes

`lem-pur-coefficient-evaluation-derived-above`: Vanishing above the extension level. Lean module `Sheaf.Paper.CoefficientEvaluationDerivedAbove`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-evaluation-derived-below`: Normalized below-level derived scalar comparison. Lean module `Sheaf.Paper.CoefficientEvaluationDerivedBelow`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-evaluation-derived-core`: The normalized derived evaluation adjunction. Lean module `Sheaf.Paper.CoefficientEvaluationDerivedCore`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-evaluation-derived-extension-coherence`: Derived truncation comparison and composition. Lean module `Sheaf.Paper.CoefficientEvaluationDerivedExtension`. The sole remaining sorry; its representative and composition argument is separated from the already proved adjunction and strict constructions.

`lem-pur-coefficient-evaluation-derived-transition`: Normalized descent of coefficient transitions. Lean module `Sheaf.Paper.CoefficientEvaluationDerivedTransition`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-evaluation-ordinary-coherence`: Termwise strict tensor and truncation coherence. Lean module `Sheaf.Paper.CoefficientEvaluationOrdinaryCoherence`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-evaluation-strict-extension`: Strict extension adjoint to coefficient-level evaluation. Lean module `Sheaf.Paper.CoefficientEvaluationModels`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-evaluation-strict-sigma`: Strict truncation inclusions with their tensor components. Lean module `Sheaf.Paper.CoefficientEvaluationStrictSigma`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-scalar-derived-adjunction`: Normalized derived quotient scalar extension. Lean module `Sheaf.Paper.CoefficientScalarDerivedAdjunction`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-tensor-derived-unit`: Universal derived comparison for the identity coefficient tensor. Lean module `Sheaf.Paper.CoefficientTensorDerivedUnit`. Proved from the recorded dependencies and elementary glue.

`lem-pur-coefficient-tensor-ordinary-coherence`: Normalized ordinary quotient tensor unit and associator. Lean module `Sheaf.Paper.CoefficientTensorOrdinaryCoherence`. Proved from the recorded dependencies and elementary glue.

`lem-pur-evaluation-transition-mate`: Iterated Hom formula for the transition mate. Lean module `Sheaf.CategoryTheory.Adjunction.CompositeMate`. Proved from the recorded dependencies and elementary glue.

`lem-pur-resolving-class-derived-adjunction`: Normalized derived adjunction from a resolving class. Lean module `Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction`. Proved from the recorded dependencies and elementary glue.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
