## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite.
Withdraw its duplicate GaloisCover.stalk_normalization_finite and attach
lem-sbc-stalk-normalization-finite to the existing, stronger upstream declaration
AlgebraicGeometry.Scheme.stalk_normalization_finite. The latter drops unused group,
cover-comparison and boundary hypotheses while proving exactly the same conclusion.
The node's mathematical statement and proof dependencies are unchanged.

Verified the entire former statement with the one-line proof
`exact AlgebraicGeometry.Scheme.stalk_normalization_finite hS c q j hCη U PA s`
in scratchpad/Replacement.lean using lcompile.py: compiled in 1.9 seconds. Both the
upstream theorem and this old-signature compatibility proof have axioms exactly
propext, Classical.choice and Quot.sound. No arbitrary witnesses or new data are introduced.

The current upstream parent was also compiled unchanged through lcompile.py in 3.4 seconds,
with no errors or warnings. The required deliver3.py --no-push preflight passed.

Change record: coord/changes/stalk-normalization-finite-retire.md.

## Proved and sorry left

The input module has zero sorry holes. Closed 0 holes; added 0 holes; split off 0.
No sorry remains in any delivered Lean declaration. This is retirement of an already proved
duplicate, not a new proof counted as hole closure. The retained upstream theorem is
axiom-free apart from propext, Classical.choice and Quot.sound.

## No longer needed

Pruned module Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite and its duplicate
AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_finite. All its imports disappear
with that module: Mathlib.AlgebraicGeometry.Geometrically.Connected,
WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor,
WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality,
Mathlib.AlgebraicGeometry.Normalization,
WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore, and
WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure.

No mathematical dependency node is pruned: the last two are still required by the retained
upstream proof. tools/downstream.py finds zero Lean consumers of the Sheaf module.
The sole proof/statement DAG parent is lem-sbc-stalk-finite-etale-model, attached to
WeilConjectures.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel. It already imports the
upstream module and proves hfin by `stalk_normalization_finite hS c q j hCη U PA s`.
Thus this is not withdrawal based only on zero importers: the existing parent's complete
replacement argument and the reattached node preserve the edge and the unit route.
Searches of lean/, quarantine/, dag/nodes/ and dag/units/ found no other mathematical parent.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an obligation split six times, but the current module
already has a complete proof and its upstream counterpart is now fully axiom-checked.
coord/retire-items.tsv lists this actual assignment as retirement, with DIFFERENT because
the source theorem has the simpler name and fewer hypotheses. That name difference does
not prevent reuse: the old signature compiles by a single application of the source theorem.
The DAG Lean attachment was stale and still named the unused Sheaf declaration.
The historical parent name in the retirement table is now an upstream module; its current
source already uses the replacement, so no parent proof adaptation is necessary.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
