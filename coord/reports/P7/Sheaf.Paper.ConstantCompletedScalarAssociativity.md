## What changed

Replaced scalarCompletion_composition's hole by a proof that localizes ordinary
balancing associativity and transports the resulting exact square through the
counit-normalized exact models of completed scalar extension.

CompletedScalarExactLocalization proves completedTensor_exact by reflection to
abelian sheaves, constructs completedTensorModel using universal left-derived
uniqueness, proves completedTensorModel_counit, and identifies scalarCompletion
with the localized ordinary square in scalarCompletion_exactModel.
ConstantCompletedOrdinaryAssociativity constructs the generic ordinaryScalarAssociator
(the specialized compositionOrdinary is in a parent that imports this item, so it
cannot be imported here) and
proves scalarCompletionOrdinary_composition by two adjunction transposes, tensor
unit naturality, and the given scalar-one balancing normalization.
CompletedScalarAssociatorLocalization isolates the compatibility between the
completed derived associator and exact localization. The original module uses
private, proved categorical lemmas to localize and transport the square.

## Proved and sorry left

Original holes closed: WeilConjectures.PurStrictScalar.scalarCompletion_composition
(one of one). This delivery is a decomposition, not a net hole reduction.

Holes added and remaining: one,
WeilConjectures.PurStrictScalar.completedTensorModel_composition, node
lem-pur-completed-scalar-associator-localization. It compares the completed
associator with the ordinary associator under exact models; it contains neither
the constant-restriction functors nor any balancing map. Its source and complete
unit-normalization proof are in its docstring and node.

The new exactness, model counit, balancing identification, ordinary associativity,
and private categorical combination proofs contain no sorry. No definitions
contain holes; the exact model is constructed by universal derived uniqueness.

## No longer needed

The proof does not use lem-fix-scalar-completion-associator or its module
Sheaf.Paper.ScalarCompletionAssociator: that statement concerns completed quotient
towers, rather than the ordinary completed scalar associator in this item.
It is removed from this node's proof dependencies, with no declaration withdrawn.

lem-pur-compact-support-coefficient-models is no longer a separate direct proof
dependency of this node: its ordinary balancing conclusion is already exposed by
CompactSupportScalarLimitReduction, which remains the public import of the item.
This does not withdraw that module or claim its remaining clauses are unnecessary.
No existing public import, existing declaration, or source-library module is removed.

## Where the brief, the DAG or earlier work was wrong

The planned scalar-completion-associator dependency does not provide the required
completed tensor associator compatibility: it compares completed quotient towers.
The exactness of ordinary completed scalar extension follows already from the
stated ordinary balancing and exact constant extension. Consequently the ordinary
square can be localized for every unbounded complex without choosing a separate
flat-term K-flat representative in the main proof.

## New nodes

lem-pur-completed-scalar-extension-exact records reflection of exactness through
underlying abelian sheaves.

def-pur-completed-scalar-exact-model records the explicitly constructed universal
left-derived comparison, and lem-pur-completed-scalar-model-counit records its
computation counit normalization.

lem-pur-constant-completed-exact-model records identification of the already
specified scalarCompletion with the localized ordinary balancing.

def-pur-ordinary-scalar-associator records the ordinary unit-normalized associator;
lem-pur-constant-completed-ordinary-associativity records the proved ordinary square.

lem-pur-completed-scalar-associator-localization is the one remaining step: transport
of the completed adjunction associator to the exact ordinary model. Its statement
is strictly a part of the original argument, independent of all balancing maps.
No change record is needed: no existing statement or definition is changed.
The blueprint unit route is retained; the unit realization record is unchanged.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
