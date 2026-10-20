## What changed

Withdrew Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite, the duplicate listed in
coord/retire-items.tsv. Redirected the sole direct consumer's private import in
Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite to the adopted source twin.
Attached lem-weil-pbc-etale-separated-stratified-finite-intermediate to the existing
upstream AlgebraicGeometry.Scheme.exists_constructible_stratified_finite.
The upstream theorem has exactly the original hypotheses, universe and conclusion;
its existing complete proof is the same argument as the withdrawn proof.
No adopted-source declaration, signature, attribute or public import is edited.
Change record: coord/changes/R3-retire-constructible-stratified-finite.md.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. No sorry remains in any delivered
module. This is duplicate retirement, not new proof progress.
AlgebraicGeometry.Scheme.exists_constructible_stratified_finite already has a complete
upstream proof; #print axioms reports exactly propext, Classical.choice, Quot.sound.
The direct consumer compiles with its proof unchanged after the import substitution.
A scratch example checks the full old theorem signature against the upstream theorem.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite, including its
private exists_immersion_of_locallyClosed helper and its duplicate public theorem.
Removed its private import from Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite,
replacing it by WeilConjectures.AlgebraicGeometry.ConstructibleStratifiedFinite.
The withdrawn file's public imports were LocallyClosedStratification,
Mathlib.AlgebraicGeometry.Morphisms.Flat, QuasiFiniteMorphism,
Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation and
Mathlib.AlgebraicGeometry.Morphisms.Finite (unqualified names here are under
WeilConjectures.AlgebraicGeometry). Its proof imports were FlatQuasiFiniteStratification,
FlatFpLqfBoundedStratification, HasUniversallyBoundedFibersOfIsLocallyQuasiFinite and
QuasiFiniteLocallyQuasiFinite, also under WeilConjectures.AlgebraicGeometry.
Those upstream modules remain needed by the canonical source theorem. No mathematical
node, upstream declaration or dependency is pruned. The only DAG parent retains the
same dependency and consumes the canonical proof through the updated node attachment.
Searches in lean/, quarantine/ and dag/nodes/ found no other direct module consumer
or node attachment. The unit sk-thm-p1 and its realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described a module with an unfinished proof. In the current
source tree it has zero holes, and coord/retire-items.tsv lists it as a duplicate of
the adopted source module. The stale DAG lean attachment still pointed to the duplicate.
The source twin now has the exact same Stratification signature, so the older DIFFERENT
classification in the retirement inventory no longer describes a mathematical mismatch.
No false statement or new mathematical issue was found. The existing proof covers the
empty base and the zero fibre-degree bound without extra hypotheses.
LeanFinder found scheme morphism and constructible-image APIs, not a shorter standalone
Mathlib stratification theorem; source search found the exact adopted theorem instead.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
