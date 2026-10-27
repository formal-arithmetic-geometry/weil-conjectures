## What changed

Proved `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPull_reflection`
with its signature unchanged in `Sheaf.Paper.CompletedPullbackReflection`.
Two private proved helpers transport unit invertibility along an isomorphism and
transport the existing quotient-completion reflector through the published
completed/constant coefficient equivalence.

Added proof-only imports of `Sheaf.Paper.CompletedConstantPresentationTransport`
and `Sheaf.Paper.StratumCompletionUnitRestriction`. The original public import
of `Sheaf.Paper.CompletedBaseChangeMap` stays. No public interface changed.
The node now records the actual strict tower and unit transport argument.
The final single-file server compile passed without warnings in 5.5 seconds.
Source inspection confirms the target signature is byte-for-byte unchanged and
all Lean lines satisfy the 100-column bound.

The source is Stacks `proetale.tex`, Tag 099N, clauses (2) and (5), together with
Tag 099M. The proof uses `ConstantCompletion.koszul_quotient_reflector`, including
its complete-output assertion, its Hom bijection, and its unit-isomorphism criterion.
`completed_constant_presentation_transport` supplies an equivalence and the specified
quotient unit equation. `stratumReduction_augmentation` supplies the strict pullback
augmentation equation for every scheme morphism, without a restriction hypothesis.
This proves the assertion for arbitrary ambient inputs, including zero objects,
empty schemes and the empty generator list; no completeness of the input is used.

Searches: LeanFinder for reflection/completion-unit Hom bijections returned generic
reflective-category lemmas, not this specified adic tower construction. Loogle for
`CategoryTheory.Equivalence.homEquiv` had no result. Mathlib grep for unit
invertibility found general adjunction facts. Searches of both library roots found
the existing constant reflector and the two normalized transport APIs used here.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPull_reflection`
(node `lem-weil-pbc-completed-pullback-reflection`).
Zero holes left in the item; zero holes added; zero statements split off.
The existing imported reflector and transport statements retain their own proofs
and obligations. This delivery proves the assigned theorem from those declarations.

## No longer needed

No existing import was removed, and no module is withdrawn or claimed globally pruned.
The original public import remains to preserve the module's exported interface.

The proof does not directly use the planned dependency
`lem-sp-completed-pullback-adjunction` (`Sheaf.Paper.CompletedPullbackAdjunction`):
its arbitrary-input reflector content is already provided by the constant reflector.
It does not directly use `prop-weil-pbc-koszul-reconstruction`
(`Sheaf.Paper.KoszulReconstruction`): the published common coefficient presentation
already retains the quotient completion and its actual unit.
It does not directly use `prop-weil-pbc-direct-image-limits`
(`Sheaf.Paper.CompletedDirectImageLimits`): the existing `stratumReductionIso` and
its augmentation equation give exactly the strict pullback comparison required.
The direct-image module still occurs through the original public import and may be
needed elsewhere; no global pruning is asserted. These three nodes were removed
from this item's direct proof dependencies. Constant completion equivalence stays.

## Where the brief, the DAG or earlier work was wrong

No statement error. The planned dependencies hid the necessary specified-unit
comparison behind larger adjunction and direct-image interfaces. The already
published common coefficient presentation and strict augmentation comparison give
a shorter direct argument. Despite its name, `stratumReduction_augmentation` is
stated for arbitrary scheme morphisms, which is essential here.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
