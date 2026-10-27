## What changed

Proved `WeilConjectures.FdPullbackWeilReturn.power_comm` in
`Sheaf.Paper.FdPullbackWeilReturnSquare`. Extract the one-step commutativity
identity from `FiniteFieldDatum.frobenius_square_cartesian`, then induct on the
positive-power index. The successor reassociates compositions, applies the
one-step identity, and applies the induction hypothesis. All existing signatures,
definitions, imports and docstrings are unchanged. This is the existing DAG
route, so no node update is required.

Validation: the item compiled through lcompile.py, exit code 0, in 17.2 seconds.
The base index zero means exponent one; the induction covers every positive
exponent and requires no additional assumption on the model morphism.

## Proved and sorry left

Closed one of the item's two holes:
`WeilConjectures.FdPullbackWeilReturn.power_comm`
(node `lem-fd-pullback-weil-return-square`).

The one remaining hole is
`WeilConjectures.fdPullbackWeilReturnSquare`
(node `lem-fd-pullback-weil-return-square`), whose statement and whole sorry proof
are unchanged. No holes were added or split off. This is a partial proof
delivery, not a proof of all three return-operator identities.

For continuation: `LocalFrobeniusTransport.rationalComposition` is the
objectwise rationalization of `integralComparisonComposition`.
`IntegralComparisonCompositionLaws` gives integral naturality and associativity;
`integralPullbackComparisonRealization` produces a system equipped with those
laws, whereas the item's parameter C is an arbitrary normalized
`IntegralComparisonSystem`. A continuation must establish the required laws
for this C from its normalized models, rather than replace it with the
existentially supplied system. The point transport is
`rationalPointIterate` followed by the fibre of `rationalReturn`; the Weil iterate
uses the specified-C compositor in `LocalFrobeniusCoefficient.iterate`.

## No longer needed

None. No imports, modules, declarations or DAG dependencies were removed.
The main theorem retains its existing proof plan and dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. The stated integral comparison theorem's
existential coherence conclusion is not directly a coherence hypothesis on the
arbitrary C supplied to this item; extracting the required rational equations
therefore involves additional work with the normalization interface.

Mathlib searches were run through msearch.py using LeanFinder, Loogle and grep.
LeanFinder found ring Frobenius iteration and Scheme.Modules.pullbackComp;
these do not state the specified rational return square. The grep results were
regular-category Frobenius reciprocity. The existing project theorem
`frobenius_square_cartesian` supplies exactly the scheme-map identity needed
for the completed helper.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
