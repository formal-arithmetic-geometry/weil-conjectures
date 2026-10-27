## What changed

The original declaration block is moved verbatim to
`Sheaf.SixFunctors.OpenSemilinearTensorModelData` and publicly reexported by the
item module. This breaks the interface/proof import cycle without changing any
existing declaration's name, signature, attributes, or definition body. The change
record is `coord/changes/A7-open-semilinear-interface-extraction.md`.

Proof-only instance overrides are scoped to the individual declarations. The
categorical tensor exactness helper keeps extension by zero abstract, avoiding
expansion of the direct-sum/sheafification implementation during rewriting.

The theorem is assembled from the ordinary generator-normalized strict comparison,
coproduct totalization, exactness and K-flat acyclicity transfer, and localization
descent. The descent proof uses a natural augmented computation on the category
of good complexes; it preserves the whole strict-system arrow and never treats
finite evaluations as faithful for maps into a derived limit.

## Proved and sorry left

Original holes: one, `WeilConjectures.OpenSemilinearTensor.openSemilinearTensorModel`.
The delivery replaces that hole by assembly from two separate construction results.
This is a decomposition, not a net proof of the target closure.

New remaining holes:

- `WeilConjectures.OpenSemilinearTensor.openSemilinearOrdinaryComparison`
  (`lem-sf-open-semilinear-ordinary-comparison`): the ordinary coefficient transport,
  generator-normalized projection formula and strict quotient comparison.
- `WeilConjectures.OpenSemilinearTensor.ordinaryReductionAugmentedComputation`
  (`lem-sf-ordinary-reduction-augmented-computation`): the natural good-model
  computation with the actual scalar-unit augmentation.

`WeilConjectures.OpenSemilinearTensor.openSemilinearReductionDescent` is proved:
whisker the ordinary chain comparison by the augmented computation isomorphisms,
then lift it through the localization of good models. Its representative square
is proved by the component formula and inverse-hom cancellation.

Edge cases checked in the new statements: identity and empty open immersions, zero
modules and complexes, coefficient index zero (the first quotient), and unbounded
complexes with odd degrees. The ordinary comparison is before localization, so it
requires no completeness. For a noncanonical ordinary reduction A, its evaluation
isomorphisms and all quotient squares transport the same scalar units; the augmented
computation statement does not assume these units can be reconstructed from arbitrary
evaluated derived arrows.

The two new construction statements are strictly separate parts of the argument:
neither has the original derived open comparison, signed total tensor, flat-term
and K-flat preservation conclusion. The remaining proof uses all of those clauses
in the original statement unchanged. There is no sorry in a definition or private
helper.

## No longer needed

No module is withdrawn. No source-library declaration is removed or changed.

The item no longer directly imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence`,
`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Mathlib.CategoryTheory.Localization.Predicate`, or
`Mathlib.CategoryTheory.Adjunction.Limits`.
The public imports of IntegralOpenReductionComparison and SemilinearDerivedSections
are retained through the public data module. RingedOpenTotalTensorKFlat remains a
proof dependency. The localization import is used in the new descent module.

The ordinary construction still needs the declared ringed slice tensor and
semilinear scalar generator arguments; these are not pruned. Good-model localization
and its universal property are used in the descent. The former direct proof plan is
organized under the new nodes, not deleted from the mathematical dependency closure.
No claim of whole-library pruning is made. The three obsolete approvals are removed
from the item node's `tool_uses`: the bilinear extension existence and uniqueness
nodes and `lem-sfb-localized-site-tensor-restriction`. These were already absent
from its reviewed generator-based proof plan; the remaining approvals retain order.

## Where the brief, the DAG or earlier work was wrong

The existing public interfaces lived in the same module as their existence theorem.
Putting separate construction results below that theorem required an interface-only
module; otherwise their imports would cycle. The extraction preserves all interface
text verbatim. The original node already had a separate definition ownership record,
whose Lean attachment is updated to the new data module.

The checks of the drafts exposed independent coefficient/site universe inference
issues and expensive unfolding of chosen scalar-extension and tensor constructions.
The complete assembly compiled in 34.7 seconds. The standalone descent compiled
without holes. All five delivery modules passed the final import-order compile with no warnings.
The delivery command also performs its own compilation and declaration-axiom audit.
The separate unchanged-consumer batch passed for
CompletedOpenTensorSystemRealization, BasicRealizationShiftSquare,
OpenRoosUnitAdjunction and OpenTensorQuotientAugmentation. That batch used the
pre-comment-fix main file; its only warning was the subsequently fixed heartbeat
comment warning. No consumer adaptation is needed.
The extracted interface block and original theorem signature were compared byte for
byte; both are identical. Every new node's Lean statement matches its module and
its proof dependencies equal the union of its proof-step uses.

## New nodes

`lem-sf-open-semilinear-ordinary-comparison` is the ordinary open projection/scalar
construction. It records coefficient transports, generator formulas and all strict
quotient equations before localization, using the existing slice-generator nodes.

`lem-sf-ordinary-reduction-augmented-computation` is the natural augmented computation
of an ordinary simultaneous quotient functor on good complexes. It records the
whole scalar-unit transpose, with finite normalization obtained by adjunction mates.

`lem-sf-open-semilinear-reduction-descent` is the proved localization assembly. Its
hypotheses separate ordinary comparison from good-model preservation. Its conclusion
is the derived representative square, obtained by the explicit conjugation and
localization universal property.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
