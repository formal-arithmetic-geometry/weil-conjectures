## What changed

Proved `AlgebraicGeometry.Scheme.relativeFiniteConstantModelIdentification` in the
assigned module, preserving its statement and public import. Added one proof import,
`import all Sheaf.Paper.PbcFinitePullbackConstructibility`, to reuse its already proved
private `relativeConstant` comparison, with no finiteness assumption.

The new private helpers explicitly construct restriction to constant scalars on the
small site, prove it fully faithful, and identify the native constant module after
restriction. The coefficient comparison is proved normalized on the constant-ring
sheafification unit using the unit equation for uniqueness of left adjoints. This
makes the identity on transported sections B-linear. Composing the fixed-module
constant comparisons and lifting through full faithfulness gives a global module
isomorphism; applying `overFunctor` gives the requested isomorphism on every slice.

Updated the item's DAG proof and dependencies to describe these constructions.
Corrected the declaration docstring's blueprint tag to the item's own node.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.relativeFiniteConstantModelIdentification`, node
`lem-weil-pbc-relative-finite-constant-model-identification`.

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
Every added private helper has a complete proof or an explicit data construction.
No intermediate unproved theorem is introduced.

Validation: the complete assigned module compiled through `lcompile.py` in 19.9 s
with exit code 0, within the 60 s per-file limit.

## No longer needed

None. The original public import and coefficient-transport dependency are retained.
The inverse-image constant comparison already exists as the proved private
`relativeConstant` declaration in `PbcFinitePullbackConstructibility`; the new proof
import reuses it instead of restating or splitting off that obligation. No module
or existing declaration is withdrawn, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous single proof step did not supply the scalar normalization needed for
the specific `relativeFiniteModelCoefficient` construction. This delivery proves
that equation and the lifting argument. The library already contained the
inverse-image constant comparison, so another split was unnecessary.

The argument uses only sheafification units, adjunctions and sectionwise identities;
it imposes no finiteness, nonzero-ring, nonempty-scheme or nonempty-slice hypothesis.
Zero modules and the zero ring are covered by the same constructions.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
