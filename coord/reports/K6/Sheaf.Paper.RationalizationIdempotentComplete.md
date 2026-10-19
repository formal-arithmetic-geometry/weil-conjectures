## What changed

Proved `WeilConjectures.rationalization_idempotent_complete` without changing its
signature, definitions, or public imports. Extract the bounded t-structure from
`WeilConjectures.rationalConstructibleStandardTStructure_existsUnique` in
`Sheaf.Paper.ConstructibleHeart`, then apply the source library's proved
`TStructure.isIdempotentComplete_of_bounded` and
`TStructure.isEquivalence_toKaroubi_and_isTriangulated_of_bounded`.
The resulting conjunction is the full original conclusion, including exactness
for the original triangulation of the raw category.

Updated the item's docstring and DAG proof to record this existing
standard-t-structure interface. This is the same bounded-t argument in the
current blueprint's opening assertion and final alternative, not a change to
the enclosing unit's route. No new mathematical statement or definition is needed.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.rationalization_idempotent_complete`
(node `lem-weil-rationalization-idempotent-complete`).
The item now has zero holes. Added zero holes and split off zero statements.
The existing input `rationalConstructibleStandardTStructure_existsUnique`
(node `def-weil-constructible-heart`) still has its pre-existing proof hole;
this delivery uses its declaration as stage 3 requires.

## No longer needed

Removed proof-only imports `Sheaf.Paper.ConstructibleTruncations` and
`Sheaf.Paper.SfRationalizationKaroubi`. The proof no longer needs
`prop-constructible-truncations` directly, nor its intrinsic/common-stage
truncation and scalar-comparison package. Its bounded-t input is the existing
legacy assertion in `Sheaf.Paper.ConstructibleHeart`, whose category and finite
coefficient field are exactly those in the item's statement.

Removed the obsolete top-level tool approval for
`prop-constructible-truncations`; retained `thm-weil-karoubian-bounded-t`.
The replacement tool is `def-weil-constructible-heart`: its standard-t-structure
clause supplies the needed input on the legacy raw category. The enclosing unit
has no separate declaration of this input. This is a request for the independent
reader/maintainer to record that tool use, not a worker-written approval.
No other nodes or modules are pruned by this delivery; the removed modules may
remain reachable through other importers.

## Where the brief, the DAG or earlier work was wrong

The item's previous first proof step says the current
`prop-constructible-truncations` declaration is on precisely
`rationalConstructibleCategory D l hl E Y`. Its current Lean declaration instead
supplies bounded t-structures on `GeneralAlgebraicallyClosedCoefficients.Stage`,
which is `sfRationalConstructibleCategory` over a small coefficient model.
`SfRationalizationKaroubi` does not identify that intrinsic category with the
legacy category used by this item's unchanged signature. No such identification
is assumed here. The existing legacy standard-t-structure assertion in
`ConstructibleHeart` already has precisely the required category, coefficient
field and finite-type hypotheses, so it is the shorter applicable interface.

Read the node's two proof steps, its dependencies, the enclosing unit record
(which has no realized step to bypass), and the current blueprint proof.
The argument covers the empty scheme and zero objects through the general
bounded-t criterion and imposes no separatedness or other extra hypothesis.

Validation: the delivered module compiled through `lcompile.py` with exit code 0,
no diagnostics, in 3.2 seconds. The first server attempt returned no response;
the retry completed normally. The signature and all public imports are unchanged;
the Lean file has no lines over 100 characters and no `sorry` tokens.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
