## What changed

Proved both remaining holes in
`Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses`.
Existence uses the already proved independently sized normalized tensorator in
`Sheaf.SecSmoothPurity.CochainTensoratorExistence`. Uniqueness is proved on inserted
pure tensors, using generalized pairs, preservation of products and sheafification.
The unit isomorphism is constructed explicitly from the inverse-image rank-one
module and sectionwise scalar multiplication, followed by sheafification; its equation
is checked on generators,
and its uniqueness follows by tensor-unit cancellation. All intermediate proofs are
complete private helpers in this module.

The duplicate comparison record abbreviates the existing common five-field record;
every normalization and universe is retained. Both theorem signatures and the
signed total-complex construction remain unchanged. The preadditivity proof reuses
`cochainModulesPreadditive`. Added only proof imports of the existing tensorator
module and the binary-product API. The common comparison-data module is also a
direct public import because the shared record abbreviation uses its type. The
original public imports remain. The change
record is `coord/changes/H7-independent-tensor-comparison-reuse.md`.

Updated the item's node proof and dependencies to match these arguments. The unit
calculation uses the forward counit formula for the localized tensor. A generic rank-one
linear equivalence constructs the inverse-image unit module. A generic private bridge
specializes the unit equation, and the pure-tensor interface stays abstract during that
specialization. Three proved private instance lemmas cache sheafification and the
underlying additive/ring composition instances within the private proof sections. The
total definitions use shared local instance bindings with the same values. No consumer
is adapted and no proof is moved into another module.

Reviewer's note (2026-10-26): the delivery also changed the unclaimed module
`Sheaf.Paper.RingedTopoiTensorComparisonData`, with explicit `HasSheafCompose` binders
and five `def` → `abbrev`. The reviewer withdrew that change and restored the published
module, for two reasons. First, the item compiles against the published module. Second,
the change broke three importers that compile against the published library:
ProEtaleInverseImageScalarUnitNormalization, RingedTensorAdjunctionMate and
CoefficientComparisonsBalancedConstruction. The withdrawal is recorded in
`coord/changes/H7-comparison-interface-abbreviations.md`.

## Proved and sorry left

Closed the two original holes:

- `SheafOfModules.CanonicalTensorPullbackOfUniverses.canonicalRingedTensorComparison_existsUnique`
  (node `lem-pur-canonical-ringed-tensor-comparison-independent-universes`).
- `SheafOfModules.CanonicalTensorPullbackOfUniverses.canonicalRingedTensorComparison_unit`
  (documented under `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`).

The final proof compiled with profiling enabled in 50.4 seconds, with all kernel
and linter checks enabled; the delivered source removes those profiling options.
Delivery checks compile the final
packet again.

Zero textual holes remain in either delivered module. Zero holes added; zero statements
split off. This is a proof delivery, not a decomposition.

## No longer needed

The old direct proof dependencies
`lem-weil-pbc-algebraic-inverse-image-tensor-comparison` and
`lem-weil-pbc-scalar-extension-tensor-comparison`, whose modules are
`Sheaf.Paper.RingedTopoiInverseImageTensorComparison` and
`Sheaf.Paper.RingedTopoiScalarTensorComparison`, are replaced by the already available
independent tensorator construction. Their modules remain in the library and the
compatibility import closure; no global module pruning is claimed. No original
import is removed. No library module or mathematical statement is withdrawn.
The unit route is retained. Removed the unused private colimit import
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`; the existing
cochain tensor colimit instances suffice. Removed the unused private helper
`UnitConstruction.unitSetIso_one`. These removals withdraw no library statement.

The duplicated expanded record body is replaced by the common record abbreviation.
No explicit consumer of the old generated constructor or projection names was found.

## Where the brief, the DAG or earlier work was wrong

The planned equal-universe comparison lemmas do not directly instantiate at
independent object and morphism universes. The existing independent tensorator is
the usable construction. The stronger generic coherence module imports this item,
so it cannot itself be imported here. The uniqueness and unit arguments are proved
locally from the construction and the original normalization conditions, without
new assumptions, weakened statements or admitted intermediate results.

The proof also keeps the sheafification functor, its adjunction and the total comparison
locally irreducible. The isomorphism proof explicitly unfolds the total comparison once;
all constructions and public signatures are preserved.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
