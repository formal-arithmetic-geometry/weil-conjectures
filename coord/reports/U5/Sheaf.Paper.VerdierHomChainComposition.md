## What changed

In `lean/Sheaf/Paper/VerdierHomChainComposition.lean`, proved the identity-test
representative and its naturality using `PodHomChain.counit_formula`. Proved the
five individual coefficient-transpose equations by a private, fully proved
adjunction calculation from the supplied counit normalization; the projection
equation is the comparison datum's recorded field. Inverted the existing
`TensorHomCoefficientTransposes.coefficient_square` for the forward-chain equation,
and combined it with the original composition hypothesis and cancellation of the
source-coordinate isomorphism to prove composition after coefficient change.
Added a private proof import of `Sheaf.Paper.TensorHomCoefficientTransposes`.
No public signature, definition, or public import changed. Updated the node's
proof to record these completed arguments and keep the remaining proof plan.

## Proved and sorry left

Closed 4 of the item's 7 original holes, all in namespace
`WeilConjectures.VerdierHomChainComposition`:

- `representing_chain`;
- `chain_naturality`;
- `coefficient_transposes`;
- `composition_after_change`.

Added zero holes and split off zero statements. The private helper
`transpose_comparison` is proved. The 3 original holes left, with their original
statements and complete existing proof-plan docstrings, are:

- `WeilConjectures.VerdierHomChainComposition.verdier_hom_chain_composition`;
- `WeilConjectures.VerdierHomChainComposition.stage_specialization`
  (marked STATEMENT-DISPUTED; see below);
- `WeilConjectures.VerdierHomChainComposition.identity_exchange`.

Each belongs to `lem-sf-verdier-hom-chain-composition`. This is a partial proof
delivery, not a proof of the remaining composition or identity law. It still
uses the stated, potentially sorry-dependent counit and coefficient-square
lemmas exactly as stage 3 permits.

## No longer needed

Removed these unused private imports from this module:

- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`;
- `Sheaf.SixFunctors.CoefIntegralFiniteExtension`;
- `Sheaf.Paper.IntegralHomReduction`;
- `Sheaf.SixFunctors.RationalOperations`;
- `Sheaf.Paper.BasicOperationsCoefficientReduction`;
- `Sheaf.Paper.PodHomChainCtfDomains`;
- `Sheaf.Paper.FiniteCoefficientHomChange`.

The coefficient calculation now uses the already stated normalized coefficient
square instead of repeating its finite/integral construction. Consequently the
item no longer directly cites the nodes `lem-coef-integral-finite-extension`,
`lem-coef-integral-hom-reduction`, `lem-fix-operation-reduction`, and
`thm-coef-finite-hom` as proof dependencies, and removes their obsolete tool-use
entries. They remain dependencies of the coefficient-square theorem; no claim
is made that they can be withdrawn from the project. The remaining composition
and identity plan retains its other dependencies. No module is withdrawn and
no globally pruned node is claimed.

## Where the brief, the DAG or earlier work was wrong

`stage_specialization` is STATEMENT-DISPUTED. Its `d : VerdierExchange.StageData`
contains an arbitrary family `projection (T) (M)` of isomorphisms, with no
naturality law in T. The first conjunct asserts that the resulting chain on
EVERY test arrow is represented by its identity-test value. This does not
follow for such a family: at field coefficients on a point, use identity
operations, the usual closed tensor and Hom, and M=N=the one-dimensional unit.
Keep the projection at its one-dimensional representing object equal to the
usual identity, but multiply its component at the two-dimensional test object
by -1. All StageData fields still hold. Its chain on a nonzero linear map
from that test object to the unit is negated, whereas inverseComponent, which
uses only the projection at the representing object, is unchanged. Thus the
first conjunct is false in this allowed case (characteristic zero). A normalized
natural projection, as in the geometric realization, is needed. The existing
statement is preserved and marked, rather than proved by an unrelated or
weaker replacement. There are no current direct Lean consumers of this
specialization lemma besides its own defining module.

The proven coefficient-transport theorem needs only the original composition
hypothesis and the coefficient square; no composition hypothesis at the changed
stage is needed for its actual displayed conclusion.

Validation: the remote single-file compile accepted the proof packet in 48.2 s.
Removed its sole unused-simp-argument warning before submitting delivery;
the delivery tool repeats the required compile and preflight checks. Lean lines
are all at most 100 characters. All public signatures and public imports match
the library source. No target or source-library file is modified.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
