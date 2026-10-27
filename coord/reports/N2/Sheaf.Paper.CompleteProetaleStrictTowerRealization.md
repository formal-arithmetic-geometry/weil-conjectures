## What changed

The item keeps the signatures of completeProetaleStrictTowerRealization and
completeProetaleStrictTowerRealization_open and supplies complete proofs of both
from the existing declared steps and one scalar compatibility step. The abstract
private theorem cbcRealizationCombine proves the endpoint cancellation and
naturality assembly without unfolding scheme-dependent coefficient data.

The already proved comparisons, evaluation, naturality, and all construction
bodies are moved into Sheaf.Paper.StrictTowerRealizationComparisons. All existing
signatures and construction bodies remain verbatim. The tower-square
normalization proof uses the existing towerSquare_localization equation before
applying the generic localization lemma, avoiding an implicit conversion through
the full specialized ringed square. Local irreducibility attributes also keep
standard derived-category and functor construction records compact. The
limit-mate invertibility proof uses local witnesses from the existing proved
corner/comparison existence theorems, avoiding nested existential elimination
through the large specialized comparison type. No witness is exported as data. Two private component equations now identify
endpoint natural-isomorphism components with the published source and target
comparisons, so naturality reuses these equations instead of expanding the
entire comparison constructions twice.
The item publicly reexports that foundation. This is needed because the declared
CompletedOpenStrictMateIdentification dependency previously imported the item
for these comparisons. Five unclaimed modules have that import redirected:
CompletedOpenStrictMateIdentification, CompletedOpenExchangeLimitNormalization,
CompletedOpenScalarLimitSquare, CompletedOpenFiniteTransposeCoherence, and
ConstantTowerSquareNormalization. The last retains import all for its proved
private comparison helper. The first and last also gain local irreducibility
attributes for standard category/functor records to avoid expensive elaborator
unfolding; all their existing declaration bodies and signatures remain unchanged. No source-library module is changed.

Both existing definition-node attachments follow their unchanged declarations
into the foundation. A construction-interface node records the other moved
comparisons and already proved auxiliary properties, so the new scalar step has
a definition dependency below the realization theorem. The parent node records the actual proper/open assembly.
The conservative module extraction and complete consumer inventory are recorded
in coord/changes/N2-strict-tower-realization-comparisons.md. No target statement,
definition data, declaration signature, or mathematical hypothesis is changed.

Validation: server compilation with lcompile.py covers all eight submitted
modules; deliver3.py performs the final clean compilation and preflight checks.

## Proved and sorry left

Original item: 2 holes. Closed in the item:

- AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_open.
  It applies completedOpenStrictMateIdentification, obtains the needed extension
  completeness from completedOpenExchangeComparison, and cancels the specified
  completed target comparison.
- AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization.
  It combines the existing actual proper normalization and its naturality,
  the open formula, the scalar/direct-image/limit square, and the fully proved
  categorical cancellation lemma.

Added: one hole, AlgebraicGeometry.Scheme.strictTowerScalarPushLimitCoherence
in Sheaf.Paper.StrictTowerScalarPushLimitCoherence
(lem-cbc-strict-tower-scalar-push-limit-coherence). This is the single normalized
scalar/direct-image/limit square on arbitrary derived strict towers. It is
strictly one part of the argument: it mentions no compactification, open factor,
proper exchange, origins, or completeness condition. Its source, full proof in
words, and edge-case checks are in its docstring and node.

No sorry remains in the item or the extracted foundation. The five import-only
adaptations preserve the one existing hole,
AlgebraicGeometry.Scheme.completedOpenExchangeLimitNormalization
(lem-cbc-completed-open-exchange-limit-normalization); no hole is added there. This is a decomposition of the main identity and a
proof of the open identity from previously stated dependencies: 2 original holes
closed and 1 new hole added. The ledger determines the import-closure change.
No transitive axiom-freedom claim is made while the
existing imported steps and the new scalar specialization remain unfinished.

## No longer needed

No library module is withdrawn or globally pruned. The proof retains the unit's
proper/open route and all canonical endpoint comparisons. The original public
imports are available through the foundation. The five redirected modules no
longer need to import the realization theorem module; they use only its already
proved comparisons. The item now privately imports CompletedOpenStrictMateIdentification
and StrictTowerScalarPushLimitCoherence.

The existing construction and auxiliary-proof dependencies remain in Step 1 of
the parent node; the extracted constructions are attached to
def-cbc-strict-tower-realization-comparisons. Their move is not mathematical pruning.

The main assembly no longer constructs finite etale-origin witnesses for j!K
or invokes Koszul reconstruction: the already proved completedExchange_mate and
restrictedExchange_mate helpers establish the actual proper normalization on
arbitrary towers. Thus prop-weil-pbc-koszul-reconstruction,
lem-weil-pbc-extension-by-zero-exact,
lem-cbc-proetale-extension-zero-comparison, and
lem-sf-comparison-pullback-exact are no longer proof dependencies of this node.
Their declarations stay in the library and may remain required elsewhere.
The generic flat-scalar coherence node is now the proof dependency of the
smaller scalar-square node. Its unused proof import is omitted from the
statement-only split module; the next worker has its declaration in the node. It remains needed; no pruning of that node is claimed.

## Where the brief, the DAG or earlier work was wrong

The open-mate dependency was already stated but imported the item for the
comparison definitions; a direct proof import would create a module cycle.
Extracting the unchanged definitions and proved auxiliary lemmas resolves that
interface problem without changing any map or theorem statement. This is a
dependency repair, not a split to evade the compile-time limit.

The published open-factor formula has no explicit completeness assumption on
j!K. The existing completedOpenExchangeComparison supplies that fact, so its
signature needs no repair. The proper normalization helpers are stronger than
the witnessed public wrapper; the original origin and completeness binders in
the main statement are retained unchanged.

## New nodes

def-cbc-strict-tower-realization-comparisons, in
Sheaf.Paper.StrictTowerRealizationComparisons, records the extracted canonical
comparison constructions and their already proved auxiliary properties. It adds
no hole and changes no construction. It gives the scalar-square node an
independent definition dependency instead of a dependency on its parent theorem.

lem-cbc-strict-tower-scalar-push-limit-coherence, in
Sheaf.Paper.StrictTowerScalarPushLimitCoherence, is the normalization
specialization of the existing generic flat scalar direct-image/limit theorem
for the exact published pro-etale comparisons. It isolates original proof Step 8
and has the Stacks 0A07 source, complete proof plan, Lean statement and search
records. The identity map, zero tower and empty scheme impose no additional
hypothesis and give the same canonical comparison square.

Change record: coord/changes/N2-strict-tower-realization-comparisons.md.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
