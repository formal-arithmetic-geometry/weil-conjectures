## What changed

Proved `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_and_isPunctuallyPureOfWeight_lowerStar_of_isFinite`
in `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual`, preserving its complete signature.
The upper-bound implication applies the existing native quasi-finite upper-bound theorem,
then `HasWeightsAtMost.of_mono` to `(lowerStarIsoHigherLowerShriekZero f F).hom`.
The purity implication applies the existing `IsPunctuallyPureOfWeight.lowerStar_of_isFinite`.
The finite-map and separated-base hypotheses synthesize every required properness,
quasi-finiteness and quasi-separatedness instance. The theorem compiled through lcompile.py
in 4.9 seconds, exit 0, without diagnostics. Empty fibres and zero stalks require no extra case:
the reused weight theorems quantify only over actual eigenvalues.

Added the private proof import `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage`.
All existing public imports, definitions, attributes and signatures remain identical.
Updated the item's proof plan and removed its two obsolete top-level tool approvals.
Recorded the existing native source calculation in one new DAG node; no Lean declaration
or module was added for it.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_and_isPunctuallyPureOfWeight_lowerStar_of_isFinite`
(node `lem-zl-finite-pushforward-punctual`). Zero local sorries remain; zero holes were added;
zero results were split off. This is a proof from existing library declarations, not a
claim that their entire transitive axiom closure is complete. In particular the existing
native characteristic-polynomial calculation uses the project's assumed trace formula.
No source-library proof or declaration was changed.

## No longer needed

Removed private imports `Sheaf.Paper.AdicPunctualWeights`,
`Sheaf.Paper.ZlFiniteAdicDirectImage`, and
`Sheaf.Paper.A1FiniteWeilSectionsDecomposition`.
This proof no longer directly needs nodes `def-weil-punctual-weights`,
`lem-zl-finite-adic-direct-image`, or `lem-a1-finite-weil-sections-decomposition` as its
planned proof inputs; the native source calculation already establishes the requisite
weight assertions in exactly the native category used by the item's statement.
The punctual-weight notion remains in the statement and in the source calculation.
Removed top-level `tool_uses` entries `lem-zl-finite-adic-direct-image` and
`lem-a1-finite-weil-sections-decomposition`.
These removals concern this module's direct proof dependencies; they do not assert that
these shared modules or their existing source-library consumers can be withdrawn.
No Lean module was deleted, and all public imports were preserved as the exported interface.

## Where the brief, the DAG or earlier work was wrong

The planned proof imports use common-stage objects, while this item's signature uses the
existing native `AlgebraicGeometry.WeilSheaf` predicates. The source already proves the
needed native quasi-finite bound and finite-image purity. The stage-2 review in the node
had in fact noted that the two clauses follow from existing declarations.
The older parent `lem-zl-quasi-finite` cites this item, so using that node as a dependency
would make a DAG cycle, despite the source proof being independent of this item.
The new node records the actual already-proved native calculation instead. Its proof uses
compact-support base change, the assumed trace formula and the positive-power norm argument;
it never invokes the finite-pushforward statement being proved. No unit statement or
unit step was bypassed: the finite-pushforward calculation remains available to its parents.

## New nodes

`lem-zl-native-quasi-finite-punctual-weights` attaches the existing proved upper-bound and
purity theorems in `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights`.
It records their actual independent characteristic-polynomial/eigenvalue proof and its
trace-formula input, with no new Lean statement, proof hole or data construction.
Its source is the existing Lean proof; its geometric assumptions and both weight
conclusions are stated explicitly. No change record is required: no interface changed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
