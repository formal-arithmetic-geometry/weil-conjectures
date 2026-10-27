## What changed

Reduced `WeilConjectures.GeneratorReduction.ordinaryRho_existsUnique` to the finite-level
ordinary scalar quotient comparison in the new module
`Sheaf.SixFunctors.ConstantScalarQuotientComparison`.
The original module now proves adjacent transition compatibility by cancelling the epic
larger quotient unit, using the actual completed quotient unit-step equation and the
constant reduction unit's naturality. `NatTrans.ofOpSequence` supplies every transition;
componentwise isomorphisms and finite-level naturality assemble the natural tower
isomorphism. Cancelling the quotient units also proves its uniqueness.
The fully proved private helper `unitNormalizedTowerIso` keeps the concrete coefficient
definitions abstract during this construction; the entire file is checked as one unit.

The first continuity instance in the private `constantSlice_isEquivalence` proof now
comes directly from the established dense-subsite instance, avoiding an expensive conversion
between concrete slice functors. Its statement and the resulting equivalence are unchanged.

The original module gained two private proof imports. No existing statement, definition, visibility or
source-library file was changed, and no consumer needs adaptation. The parent node's
Step 5 records this finite-to-tower reduction. The existing thirteen-step route and all
other obligations remain in place.

Validation: server `lcompile.py` accepted the main module in 48.9 seconds. The new
finite quotient module also compiled after narrowing its public imports. No profiling
options or experimental attributes remain.

## Proved and sorry left

Original holes: 11. Original hole closed: `WeilConjectures.GeneratorReduction.ordinaryRho_existsUnique`.
New hole: `WeilConjectures.GeneratorReduction.ordinaryScalarQuotientComparison`
(node `lem-sf-constant-scalar-quotient-comparison`).
This is a decomposition: one hole closed and one strictly finite-level hole added,
so the net hole change is zero. The new statement asserts neither compatibility between
indices nor a tower or derived comparison. The Lean proof supplies the missing strict
transition compatibility, naturality and uniqueness. All choices of finite comparisons
are local to a theorem proof; the public `ordinaryRho` remains selected by the unchanged
unique characterization.

Ten original holes remain, all attached to
`lem-sf-constant-semilinear-generator-comparison`:

- `WeilConjectures.GeneratorReduction.rho_existsUnique`
- `WeilConjectures.GeneratorReduction.ordinarySystemDirectIso_existsUnique`
- `WeilConjectures.GeneratorReduction.ordinaryIntegralDirectIso_existsUnique`
- `WeilConjectures.GeneratorReduction.systemDirectScalarIso_existsUnique`
- `WeilConjectures.GeneratorReduction.ordinarySystemPullMap_isIso`
- `WeilConjectures.GeneratorReduction.integralDirectScalarIso_existsUnique`
- `WeilConjectures.GeneratorReduction.systemOpenScalarMap_isIso`
- `WeilConjectures.GeneratorReduction.ordinaryIntegralPullMap_isIso`
- `WeilConjectures.GeneratorReduction.integralOpenScalarMap_isIso`
- `WeilConjectures.GeneratorReduction.constantSemilinearGeneratorComparison`

## No longer needed

None. No import or node was withdrawn: the untouched proper/open and derived comparison
holes still retain their recorded route. The new finite-level lemma replaces only the
unformalized finite step within the ordinary tower argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The existing Step 5 bundled a
finite scalar quotient calculation with the transition gluing and uniqueness. These are
now separated, with the latter implemented in Lean. The new lemma uses the existing
constant-completion, scalar-adjunction and small-site constructions rather than choosing
new coefficient objects. Zero modules, empty site objects, and the first positive
quotient (n = 0) obey the same quotient argument. The tower proof uses adjacent arrows
and obtains all arrows by the natural-transformation constructor, not by assuming
faithfulness of derived finite evaluation.

## New nodes

`lem-sf-constant-scalar-quotient-comparison` states the finite ordinary quotient comparison
and epimorphy of its scalar unit after the fixed small-site transport. Its source and
complete quotient proof in words appear in its declaration docstring and node. It is strictly
below the whole strict-tower existence/uniqueness result. It uses the existing generic
quotient and scalar-adjunction tools without changing the unit route. Existing interfaces are unchanged; no change record
is needed.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
