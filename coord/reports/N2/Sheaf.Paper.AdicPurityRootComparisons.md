## What changed

Completed the two remaining proofs in `Sheaf.Paper.AdicPurityRootComparisons`.
The etale diagonal is the cast of the specified generic diagonal across equalities
of its source and target recursions; heterogeneous equality proves uniqueness.
The root quotient family uses the existing normalized first-line scalar reduction,
the positive tensor comparison recursion, and scalar-extension embeddings. Uniqueness
uses root tensor generation at one and ordinary tensor generation at higher powers.
Added proof-only imports of `SignedTwistFirstReduction`, `SignedLineScalarTensorTower`
and `PurTwistIntegralLocalModels`; the latter two use `import all` to reuse their
already proved private positive-comparison and identity-on-sections helpers.
All existing types, public imports, hypotheses and unit routes are preserved.
The three etale diagonal signatures use the existing ordinaryFiniteDegreeZero
interface, definitionally equal to their original singleFunctor.obj expression.
The predicate uses the new explicitly typed adicPurityEtaleDiagonalModel, whose body
is exactly the old generic diagonal with the original unit comparison; this
substitution is definitionally equal. Its explicit source and target types check
the derived-category instances and constant-sheaf tensor-unit identification once.
A proved private helper establishes the diagonal comparison
over an arbitrary coefficient ring, avoiding repeated kernel normalization of the
concrete p-adic quotient while checking the argument. The item node now records
the completed arguments and the existing nodes whose declarations they use.
No other module is adapted. Definition-interface change record:
coord/changes/adic-purity-etale-diagonal-interface.md.

## Proved and sorry left

Closed `WeilConjectures.adicPurityEtaleDiagonal_existsUnique` and
`WeilConjectures.adicPurityRootQuotients_existsUnique`, both attached to
`def-pur-adic-root-comparisons`: 2 of 2 original holes closed, zero holes added,
zero holes left in the delivered module. No split-off theorem. The complete module compiled successfully through lcompile.py
in 45.0 seconds; profiling options were then removed for delivery.

## No longer needed

No existing import, node or module is removed. No primitive-root trivializing cover
or rank-one local-freeness result is needed for the positive quotient-family proof:
scalar extension commutes with arbitrary positive tensor powers, and the original
root tensors already detect equality after restricting to the integral constants.
The existing flatness and finite-site comparison dependencies remain needed by the
other retained declarations. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old unfinished quotient-family proof described a primitive-root cover to prove
uniqueness. This is unnecessary and would introduce an invertibility assumption
absent from the statement. The unconditional, already proved first-line quotient
comparison and tensor generation prove exactly the original statement, including
zero powers, zero section rings, and the empty scheme. No statement repair is needed.
The kernel profiling trace identified repeated normalization of the concrete
coefficient ring; the diagonal argument is therefore proved first with that ring
abstract. The typed diagonal interface and existing stable degree-zero interface
avoid repeated normalization of derived single-functor objects; both changes are
definitionally identical to the original expressions. A declaration-use search reports only this item as a direct user of
the three declarations with adjusted type spelling, so no consumer adaptation is required.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
