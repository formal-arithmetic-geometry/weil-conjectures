## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.compositionRefinement_isIso` and
`AlgebraicGeometry.ProEtale.StrictTower.compositionRefinementExchange` in the item.
The first factors the hf refinement map through `gamma_isIso` and canonical
isomorphisms, then obtains horizontal invertibility by cancelling the composition
maps in the existing refinement equation. The second applies the declared
`refinementExchangeCoherence` to f, h and hf and combines the first two squares
by naturality. Its equations hold on every input. A proved private helper constructs
a genuine finite scalar etale origin for zero (using the finite zero ring) to supply
the unrelated input required by the dependency's other conjuncts. No data are chosen
from an unproved mere existence statement.

Moved the existing canonical map definitions and the refinement/base-change
structures, with signatures and bodies verbatim, into the new module
`Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps`. The item publicly reexports
it. `Sheaf.Paper.RefinementExchangeCoherence` changes only its public import from
the item to this shared module. This permits the item's private proof import of
the already-declared sibling theorem without an import cycle. Server preflight identifies H4 as the sibling
holder; its statements, constructions, proofs and existing hole are untouched.
No source-library file or target statement changes.

Updated the item's node's Lean note and proof step 10 with the implemented auxiliary
arguments. The original remaining proof steps and their dependencies are retained.
Change record: `coord/changes/D2-strict-tower-composition-map-extraction.md`.

Validation: all three delivery modules compile together through `lcompile.py --all`.
The moved construction bodies were compared against the repository byte for byte;
the sibling was checked to differ by precisely its one import line. No private
helper has a hole, and no definition has a hole.

## Proved and sorry left

Closed 2 of the item's 4 original holes:

- `AlgebraicGeometry.ProEtale.StrictTower.compositionRefinement_isIso`.
- `AlgebraicGeometry.ProEtale.StrictTower.compositionRefinementExchange`.

Two original holes remain unchanged, both attached to
`lem-cbc-complete-proetale-composition-pasting-coherence`:

- `AlgebraicGeometry.ProEtale.StrictTower.compositionPastingCoherence`.
- `AlgebraicGeometry.ProEtale.StrictTower.compositionCommonCoherence`.

Added holes: 0. Split-off statements: 0. These are proofs from the existing stated
dependencies, not claims of axiom-free closure: the first uses the existing
`compositionPastingCoherence`, and the second uses the existing
`refinementExchangeCoherence`. The latter's original hole, in the adapted sibling,
remains unchanged and belongs to
`lem-cbc-complete-proetale-refinement-exchange-coherence`.

## No longer needed

The item's three original public imports now belong to the shared map module and
remain publicly reexported. The following original private imports are no longer
direct imports of the item or shared map module:

- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`.

The completed proofs use the shared public interface, the sibling dependency and
`Mathlib.Algebra.Ring.PUnit`. The original public import edge from the sibling to
the item is replaced by the edge to the shared map module.

No DAG node or module is withdrawn or declared unnecessary: the main pasting proof
still has its original finite-origin, compositor and calculus obligations, and
the remaining common-refinement proof still needs the declared independence result.
The shared-map extraction does not authorize pruning the item or its DAG parents.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly lists the sibling refinement/exchange result as a proof dependency,
but the original Lean placement of their shared definitions made that dependency
impossible to import back into the item. Extracting the definitions resolves this
implementation cycle without weakening anything or duplicating any operation.

The common-refinement transport equation was also explored, but conversions between
the two inverse-map presentations caused expensive derived-category unfolding and
kernel timeouts. Those experiments and temporary partial proofs are not in the
delivery. The two remaining original named statements and their complete proof plans
are preserved rather than replaced by renamed or repackaged holes.

## Forced adaptations

`Sheaf.Paper.RefinementExchangeCoherence` is held by H4 (server preflight).
Only line 8 changes, from `public import Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting`
to `public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps`.
The item's new proof needs the declared sibling theorem. With the original sibling
source and the changed item source, `lcompile.py --all` fails with exactly:

```
the modules import one another in a cycle: Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting, Sheaf.Paper.RefinementExchangeCoherence
```

The adapted sources compile in order Maps, RefinementExchangeCoherence, Pasting.
The changed line is necessary to break this source dependency cycle. An isolated
recompile of the original sibling against previously compiled adapted artifacts
passes: that cached test does not rebuild the mutually importing sources, so it
is not evidence that the original source graph can compile together. This distinction
is disclosed for the independent reader. No signature or visibility of a declaration,
or any other line of the sibling, changes.

## New nodes

`def-cbc-strict-tower-composition-maps` attaches the extracted F/D/C/E definitions,
refinement and base-change structures, and their whiskered maps. It is a definition
node with real constructed data and zero holes, not a split-off unproved theorem.
The existing coherence node now lists this definition as a dependency, and its Lean
attachment retains the declarations physically remaining in the item. The blueprint
search found no separate canonical-map node; the old coherence node contained both
the definitions and the theorem statements, and this extraction separates those parts.
Change record: `coord/changes/D2-strict-tower-composition-map-extraction.md`.

## Forced adaptations

### Sheaf.Paper.RefinementExchangeCoherence
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
