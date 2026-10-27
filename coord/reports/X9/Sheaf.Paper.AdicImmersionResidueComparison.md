## What changed

The fixed residue-pullback definition and its exactness instances were moved to the
small core module `AdicImmersionResidueComparisonCore`; the item module keeps an
abbreviation with the original public name.  The parent theorem now assembles two strictly smaller named comparison theorems,
`sfbImmersion_residueComparison_fixed` and `sfbImmersion_residueComparison_etale`,
from private proof imports.  The original target statement and public interface are unchanged; the implementation
of the fixed residue pullback moved to the core module behind an abbreviation.

## Proved and sorry left

The parent declaration `AlgebraicGeometry.Scheme.sfbImmersion_residueComparisons`
is proved by conjunction introduction from the two clause declarations.  Two
strictly smaller obligations remain as named public theorems:

- `AlgebraicGeometry.Scheme.sfbImmersion_residueComparison_fixed`, node
  `lem-sfb-adic-immersion-residue-comparison-fixed`;
- `AlgebraicGeometry.Scheme.sfbImmersion_residueComparison_etale`, node
  `lem-sfb-adic-immersion-residue-comparison-etale`.

## No longer needed

No existing imports or DAG dependencies were removed.  The parent proof uses the
core data module and the two new clause modules.  The original finite-comparison
proof dependencies remain available through the split obligations.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan describes the finite derived comparison and etale pullback
arguments but no existing Lean declaration states either resulting comparison
isomorphism.  The two clauses therefore had to be made explicit as separate,
strictly smaller obligations before the parent conjunction could be assembled.

## New nodes

`lem-sfb-adic-immersion-residue-comparison-fixed` records the fixed completed-model
clause and is implemented by
`lean/Sheaf/Paper/AdicImmersionResidueComparisonFixed.lean`.

`def-sfb-adic-immersion-residue-comparison-core` records the moved fixed residue
pullback data and is implemented by
`lean/Sheaf/Paper/AdicImmersionResidueComparisonCore.lean`.

`lem-sfb-adic-immersion-residue-comparison-etale` records the etale-origin clause
and is implemented by
`lean/Sheaf/Paper/AdicImmersionResidueComparisonEtale.lean`.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
