## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.smallIntegralRoosCompletenessTransport`
without changing its statement or its existing public imports. The proof uses the proved
ordinary-coefficient `internal_completion_stacks_comparison` and
`IntegralModelsStacks.completion_transport`, rather than redoing the local completion
comparison. Private helpers transport the local predicate through derived isomorphisms and
cancel the absolute/spectral coefficient restrictions.

Added `Sheaf.Paper.SmallIntegralRoosComparison`. It tensors compatible finite quotient
module isomorphisms with each term, passes to preserved products, intertwines one minus
shift, and compares the two biproduct coordinates of the differential and augmentation.
This explicitly preserves the zero shifted-product augmentation coordinate. The main proof
chooses a flat-term K-flat representative, uses the existing monoidal equivalence theorem
to preserve K-flatness, and reflects the resulting quasi-isomorphism through scalar
restriction.

Added `Sheaf.Paper.SmallIntegralFiniteQuotientTransport` for the ordinary finite quotient
module calculation and its unit/transition normalization. It has no complexes,
K-flatness, Noetherian, completeness or constructibility hypothesis. Its positive levels
start at exponent one. Named local caches use the existing canonical sheaf tensor,
closed and relative-module tensor constructions with explicit universe arguments.
The condensed ring isomorphism need not fix a chosen uniformizer:
preservation of the unique maximal ideal is sufficient. The empty scheme gives zero
modules and satisfies the same formulas.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.smallIntegralRoosCompletenessTransport` is replaced by a
complete proof from the finite quotient comparison. The new
`AlgebraicGeometry.ProEtale.smallIntegralRoosComparison` has a complete proof.

One hole is added and remains:
`AlgebraicGeometry.ProEtale.smallIntegralFiniteQuotientTransport`, node
`lem-sfb-small-integral-finite-quotient-transport`. Its docstring gives the point-evaluation,
maximal-ideal-power, quotient, continuity and module-linearity argument.

Hole accounting in the changed files: one original hole closed and one strictly simpler
hole added; this is a decomposition, with net zero holes closed in these files.
This is not a claim about the ledger's target-import-closure baseline.
All three files passed the full-sandbox compiler. Temporary profiling options were
removed before delivery; the delivery tool supplies the final compile and preflight checks. The residual statement is ordinary coefficient
algebra, rather than the original derived-completeness implication under a new name.

## No longer needed

No original public import was removed and no module is withdrawn. The original node no
longer directly invokes `lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-proetale-countable-products-exact`, or `lem-weil-strict-roos-comparison`:
the existing ordinary completion comparison supplies those steps. Their modules remain
needed by that comparison, so this delivery claims no global pruning of them.

The coefficient-DVR and profinite-tower arguments now belong solely to the finite
quotient module node; the main theorem does not import additional coefficient arithmetic
modules to repeat them. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically appropriate, but its local-completion and
unbounded representative-independence steps are already proved for ordinary coefficients.
Reusing those statements isolates the actual independent-universe issue in the finite
quotient modules. No statement was disputed, weakened or repaired. No adopted source
module was changed.

## New nodes

`lem-sfb-small-integral-finite-quotient-transport` records the positive quotient module
isomorphisms and their unit and transition identities. It is the only residual hole and
is strictly below the original argument's first step.

`lem-sfb-small-integral-roos-comparison` records the proved transport of the explicit
augmented Roos complex from these module comparisons. The original node's proof,
proof dependencies and proof origin were updated to follow the implemented route.
There are no change records, since no existing statement or definition is changed.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
