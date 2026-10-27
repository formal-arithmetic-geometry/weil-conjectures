## What changed

Filled five existing theorem proofs in
`Sheaf.Paper.StratumCompletionUnitRestriction`. All eleven theorem signatures,
all existing definitions and the three public imports remain unchanged.

* `stratumFiniteCoefficient_naturality`: transport naturality through the published
  constant-system comparisons, for arbitrary ordered levels including equal levels.
* `stratumRestriction_limits`: handle the four restriction cases on set inverse image,
  transfer limit preservation through abelian and module forgetful functors, then use
  the scalar-extension equivalence. Reuse exactness and the coefficient projection square.
* `stratumCompletionComparison_unit`: prove the equation for the specified map by
  adjunction-unit naturality, constant/pullback naturality, the source counit triangle
  identity, and `stratumReduction_augmentation`; infer invertibility from the existing
  limit-comparison obligation and the strict tower isomorphism.
* `stratumIntrinsicComplete_preserved`: apply the already published
  `completedKoszulQuotientComparison` to the two supplied representatives and cancel
  the comparison isomorphisms.
* `stratum_completion_unit_restriction`: prove preservation and reflection. For reflection,
  use the same normalized unit comparisons and detect the global quotient unit by its
  cone. Private proved helpers construct the natural underlying-abelian comparison and
  deduce unbounded derived detection from the existing abelian stratum-cover theorem.

Added only proof imports and proved private helpers. `import all` accesses existing proved
private comparison and limit-preservation helpers, without changing their owning modules.
Updated the item node's proof, dependencies and proof origin to match these arguments.
No new nodes, statement changes, definition changes, or consumer adaptations.

## Proved and sorry left

Closed 5 of the original 11 holes; added 0 holes; 6 holes remain. This is a partial
proof delivery, not a decomposition. The five closed declarations are:

* `AlgebraicGeometry.Scheme.stratumFiniteCoefficient_naturality`
* `AlgebraicGeometry.Scheme.stratumRestriction_limits`
* `AlgebraicGeometry.Scheme.stratumCompletionComparison_unit`
* `AlgebraicGeometry.Scheme.stratumIntrinsicComplete_preserved`
* `AlgebraicGeometry.Scheme.stratum_completion_unit_restriction`

The six remaining declarations retain their original full named theorem proofs
`by sorry`, source references, and complete natural-language proof docstrings.
Each belongs to node `lem-weil-pbc-stratum-completion-unit-restriction`:

* `AlgebraicGeometry.Scheme.stratumModuleReductionIso_exists`
* `AlgebraicGeometry.Scheme.stratumReductionIso_exists`
* `AlgebraicGeometry.Scheme.stratumReduction_normalization`
* `AlgebraicGeometry.Scheme.stratumReduction_evaluation`
* `AlgebraicGeometry.Scheme.stratumReduction_augmentation`
* `AlgebraicGeometry.Scheme.stratumRlimComparison_isIso`

The newly filled upper proofs still depend on those existing named obligations.
They do not establish axiom-free completeness of the entire module.

## No longer needed

Removed direct proof imports:

* `Sheaf.Paper.ConstantCompletionEquivalence`
* `Sheaf.Paper.ExactProductFunctorStrictLimit`
* `Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat`
* `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
* `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`

No declaration from these imports is used directly by the five new proofs.
The remaining ordinary/derived tower and Rlim obligations retain their original
mathematical dependencies, including constant completion, normalized strict-tower
pullback, exact products and the exact-product strict-limit comparison.
Those dependencies are not claimed to be globally pruned.

The restriction-limits step now does not need
`lem-sfb-ringed-site-restriction-kflat` or
`lem-weil-proetale-weakly-etale-localization`: the existing exact module pullback
instances and the canonical underlying comparisons prove the statement directly.
Removed those two obsolete tool approvals and their proof-dependency entries.
No module is withdrawn; no assertion is made that a module leaves the global closure.
The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing Koszul/quotient comparison is already stated in the actual completed
coefficient presentation, so reconstructing it through the much larger constant
completion interface is unnecessary for preservation and detection.

The previously planned slice-site restriction proof of all-limit preservation is
unnecessary once the existing set-limit, underlying-abelian and scalar-equivalence
comparisons are used. All four composite cases are handled without a Noetherian
hypothesis on the restricted scheme.

`PulledReductionNormalizationComparison` cannot be imported here because it already
reaches this item; its elementary finite-ring naturality calculation was adapted
locally instead. No import cycle, source-library edit or new axiom is introduced.

Validation: all existing theorem signatures were compared byte-for-byte with the shared
source and are unchanged. The DAG proof-dependency list is exactly the union of step
uses. Every delivered Lean line has at most 100 characters. The final server compilation passed in 12.1 seconds. The delivery preflight
provides the final packet and axiom checks.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
