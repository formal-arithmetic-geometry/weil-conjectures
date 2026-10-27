## What changed

Filled all three theorem proofs in `Sheaf.Paper.IntegralScalarExtension`.
`integralCompletedScalarMap_existsUnique` builds the compatible finite quotient
cone, lifts it to the inverse limit in ring sheaves, and uses the fully faithful
forgetful functor to retain commutativity. Joint monicity proves uniqueness.
The construction is the already proved one in
`FiniteFreeCompletedScalarComparison`, reproduced here because importing that
downstream module would create a cycle.

`integralOrdinaryScalarWitness` extracts the specified ordinary functor, object
and morphism equalities, and additivity from
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients`.

`integralOrdinaryScalar_exact` applies `completedIntegralFiniteFree` to the
specified completed coefficient map. The basis-induced tensor isomorphisms and
their proved naturality identify ordinary extension followed by restriction
with `finitePowerFunctor`. Finite powers preserve finite limits and colimits.
Restriction preserves both and reflects isomorphisms, so it reflects those
limits and colimits, proving exactness of ordinary extension itself.
A proved private helper carries out the general finite-free argument before
specializing to completed coefficient rings, avoiding expensive unfolding of
the inverse-limit definitions. The proof uses private proof imports
`CompletedIntegralFiniteFree` and `import all FiniteFreeScalarExtension`; no
public interface changes.

## Proved and sorry left

Closed 3 of 3 holes:

- `WeilConjectures.integralCompletedScalarMap_existsUnique`.
- `WeilConjectures.integralOrdinaryScalarWitness`.
- `WeilConjectures.integralOrdinaryScalar_exact`.

All three have the existing docstring node
`def-weil-integral-scalar-extension`. No holes remain in the item; no holes were
added and no intermediate results were split off. All definition bodies and
existing declaration signatures remain unchanged.

## No longer needed

None. No existing imports or DAG dependencies were removed, and no modules
were withdrawn. The initial public imports are retained as the existing public
interface. The proof needs no new unproved mathematical statement.

## Where the brief, the DAG or earlier work was wrong

The definition node's current Lean attachment is the universe-independent
wrapper `IntegralScalarExtensionUniverses`, which publicly imports this item;
there is no node whose current `lean.module` is exactly this module. The three
holes still carry `def-weil-integral-scalar-extension` in their docstrings.
Its original proof list was empty. Its sandbox node now records the existing
well-definedness construction and the three completed API proofs, with precisely
their proof dependencies; its statement, Lean attachment and unit route are unchanged.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
