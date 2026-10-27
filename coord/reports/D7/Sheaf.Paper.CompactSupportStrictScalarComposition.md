## What changed

Reduced `WeilConjectures.PurStrictScalar.completedArrow_existsUnique` in
`Sheaf.Paper.CompactSupportStrictScalarComposition` without changing its statement.
The proof takes existence, its normalization equation, and target completeness
from the existing `compactSupportScalarLimitReduction`. It cancels the two
specified comparison isomorphisms and uses complete-target injectivity of
constant restriction for uniqueness. Added the private proof import
`Sheaf.Paper.CompactSupportCompleteRestrictionFaithful`.

The new module states only the missing map-detection step. It has no compactification,
scalar-extension pair, finite-Tor input, support functor, or gamma normalization
in its statement. Its source and expanded Cech argument are in its docstring and node.
Its interface uses raw `SheafOfModules.restrictScalars.mapDerivedCategory`, with
the exactness structures and the constant-module derived-category structure explicit,
using the standard completed-module derived category. Existing instances supply these
structures at the application. It imports only completeness and the coefficient map.
The sandbox's two modules compiled together through lcompile, exit code 0.

## Proved and sorry left

Original holes: 8. Closed in the item: 1, `completedArrow_existsUnique`, by a
compiling reduction. Added holes: 1. Net holes closed: 0. This is a decomposition,
not a claim that the mathematical uniqueness theorem is now sorry-free.

Seven unchanged original holes remain, all in namespace
`WeilConjectures.PurStrictScalar`, node
`lem-pur-compact-support-strict-scalar-composition`:

- `compositionProper`
- `compositionOpen`
- `compactSupportStrictScalarComposition`
- `compactSupportScalarLimitComposition`
- `compactSupportCompletedScalarComposition`
- `compactSupportStrictScalarIdentity`
- `compactSupportCompletedScalarIdentity`

One new hole remains:
`WeilConjectures.PurStrictScalar.scalarConstantRestriction_complete_map_injective`,
node `lem-pur-complete-constant-restriction-map-injective`.
The already proved coefficient, arithmetic and naturality clauses remain proved.
Every remaining sorry is a named public theorem; none is inside a definition.

## No longer needed

None. No imports, nodes, modules, declarations or dependencies were removed.
The original dependencies still support the seven unchanged holes and their plans.
The new proof uses the existing scalar-limit reduction directly; no downstream
integral coefficient comparison is imported.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure found. The first preflight detected a DAG
cycle caused by naming the scalar-limit-reduction node as the new lemma's
statement dependency (through its existing compact-support dependencies).
The new lemma now uses raw coefficient restriction and minimal imports,
and cites the acyclic completed-constant presentation transport instead of
the compact-support coefficient-model theorem. The completed-arrow uniqueness docstring
calls for a complete-object restriction argument, but no directly usable map-injectivity
statement at this universe-correct API was present. This delivery exposes precisely
that step, and proves the existence-and-uniqueness combination in Lean.
The new lemma only assumes completeness of its target; its proof sketch explains
that slightly stronger one-sided form via the restriction/coinduction unit.
Checked zero source, zero target, empty scheme and shifted objects. It does not
assert faithfulness of finite evaluation or of arbitrary derived restriction.
The binding unit's route is unchanged.

## New nodes

`lem-pur-complete-constant-restriction-map-injective`, module
`Sheaf.Paper.CompactSupportCompleteRestrictionFaithful`: restriction along the
canonical constant-to-completed coefficient map detects maps into complete targets.
Source: Stacks Tag 099I, `lemma-restriction-derived-complete-equivalence`, Cech
construction. The node includes actual LeanSearch, LeanFinder, Loogle and grep searches;
blueprint keyword search found no exact duplicate. Its proof plan explains why the
restriction/coinduction unit at the target is invertible and how adjunction then
detects maps. No existing statement or definition changes and no change record.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
