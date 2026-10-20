## What changed

Completed `Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange` without changing
its two public theorem signatures, universes, public imports, or the exchange definition.
The proof follows the existing node's connected-chart route (unit `sk-prop-deg0`):
construct the restriction/composition comparisons with their unit equations, apply the
set-valued connected-fibre sections theorem twice, identify the canonical exchange on
charts, and apply the existing covering-family sheaf isomorphism criterion. The smooth
case applies the flat case using the smoothness instances.

The private comparison proofs adapt the proved source implementations in
`WeilConjectures.AlgebraicGeometry.EtaleChartSectionsObjectComparison` and
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` to sets. The restriction
comparison is constructed explicitly by uniqueness of left adjoints, and composition
by conjugating direct-image composition; no arbitrary witness or new public object is
introduced. Local irreducibility of the pullback construction and the two comparisons,
and explicit naturality arguments, keep elaboration within the single-file limit.

Added private imports of `WeilConjectures.Mathlib.CategoryTheory.Sites.LocallyBijective`
and `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`. Updated the existing
node's proof and proof origin to describe the implemented comparisons and gluing. The
mathematical route and its proof dependencies are unchanged. No consumers need adaptation.
The static interface checker records the added `open` and local elaboration commands;
`coord/changes/etale-set-degree-zero-proof-commands.md` documents these commands and
the five downstream consumers. No public signature or mathematical meaning changes.

Validation: the module compiles cleanly through `lcompile.py`. A separate scratch probe
of both public declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
All added import directions were checked and have no cycles. No extra hypothesis on the
base-change morphism or coefficient sheaf is used; empty covers are handled by the same
covering-family criterion.

## Proved and sorry left

Closed both original holes (node `sbc-lem-degree-zero-flat-base-change`):

- `AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_flat`.
- `AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_smooth`.

Original holes: 2. Closed: 2. Added: 0. Split off: 0. Remaining in the module: 0.
Both proofs have no transitive `sorryAx`, as confirmed by `#print axioms`.
Every private helper is proved; all private definitions are explicit constructions.

## No longer needed

Removed these redundant proof imports:

- `Mathlib.RingTheory.FiniteStability`.
- `Mathlib.CategoryTheory.Limits.MorphismProperty`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.

The first four and last two APIs are already available from the retained imports. The
restriction import is replaced by the localization adjunction's defining module: its
comparison and unit equation are explicitly constructed in private helpers. The generic
composition and restriction inputs of the DAG are implemented by these same adjunction
constructions, preserving the node's mathematical route. No node or library module is
withdrawn or claimed to be globally unreachable. Existing public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The `blueprint_update` proof says reduced connected components of fibres are geometric
points; this is false (an affine line over an algebraically closed field is connected and
has many geometric points). The existing six-step DAG proof and the unit's connected-chart
route already correct that error. This delivery follows that route and the actual source
proofs: Stacks `0EYS`, `lemma-fppf-reduced-fibres-base-change-f-star`; `0EZX`,
`lemma-base-change-f-star-general`; `0EY5`, `lemma-cover-by-geometrically-connected`.
No statement correction is required.

The shortest-route searches were run through `msearch.py` (LeanFinder, Loogle, grep)
and repository `rg`. They found no direct set-valued theorem. The existing module-valued
base-change theorem cannot be applied to arbitrary sheaves of sets; its elementary
comparison and covering argument can, and were adapted here. No new nodes or mathematical statements are needed. The command-only
change record named above is included for the static interface check.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
