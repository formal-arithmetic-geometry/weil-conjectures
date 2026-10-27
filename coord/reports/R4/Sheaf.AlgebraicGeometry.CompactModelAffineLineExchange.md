## What changed

Proved AlgebraicGeometry.Etale.compactModelAffineLineExchange by factoring the affine-line
projection through its standard open chart in the projective line. The composition theorem
for canonical exceptional exchange combines the proved open-immersion case with the existing
projectiveLineExceptionalBaseChange. The original statement, including its field argument,
is unchanged. The proof works uniformly for all complexes and for an empty affine base.

Removed three broad public-import occurrences from the two unclaimed shared Sheaf modules
ProjectiveLineTraceModel and ProjectiveLineExceptionalBaseChange, replacing them with
UpperShriekBaseChange and a proof-only MatesCounit import. These unused imports caused an
actual cycle through Finiteness.Deligne and this item. All declarations and proofs of those
two modules remain verbatim. No source-library module is changed.

Updated lem-asd-compact-model-affine-line-exchange's proof, proof_deps and proof_origin to
record the existing projective-line theorem and canonical mate-pasting argument. The unit
route is preserved: projective-line duality followed by restriction to the affine chart.

Validation: lcompile.py accepted the item, both revised shared modules, and all four
unchanged direct importers. The item compiled in 48.7 seconds and SmoothBaseChange in
46.5 seconds. Both the revised Lean import graph and the revised DAG dependency graph
were checked for paths back to this item; neither has a cycle. Temporary consumer copies
and profiling options are removed before delivery.

Change record: coord/changes/R4-projective-line-exchange-import-cycle.md.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Etale.compactModelAffineLineExchange
(lem-asd-compact-model-affine-line-exchange).

The item has zero remaining sorry. Added zero holes and zero split-off statements.
The two other delivered modules already had zero holes and still have zero.
The proof uses existing projective-line declarations, including the separately assigned
exists_presentedFiniteP1TraceAdjunction; no claim is made that all transitive dependencies
are already sorry-free. This delivery is a proof from existing declarations, not a new
split or an axiom-free closure of that entire dependency tree.

## No longer needed

Removed these public-import occurrences:

- WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineBaseChange
  from Sheaf.SixFunctors.ProjectiveLineTraceModel.
- WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineKunneth
  from Sheaf.SixFunctors.ProjectiveLineTraceModel.
- WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineBaseChange
  from Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange.

The item no longer needs direct dependencies on thm-amb-p1-adjunction,
lem-amb-cartier-kummer-map or thm-amb-p1-decomposition, nor imports of their modules
ProjectiveLineFullAdjunction, CartierKummerMap and OrdinaryFiniteP1Decomposition.
The existing projective-line exchange theorem already assembles the relevant normalized
finite splitting, diagonal adjunction and counit compatibility. Retained
lem-weil-pbc-mate-pasting for the canonical composition law. No declarations or modules
are withdrawn, and the removed imports' modules remain needed elsewhere in the library.
No new imports were added solely for an unused dependency.

## Where the brief, the DAG or earlier work was wrong

The old search found the source affine-line implementation unusable because of an import
cycle. Its mathematical argument is reusable: the cycle came from unused high-level
imports in two Sheaf modules, rather than the projective-line theorem's actual proof.
The originally cited full adjunction is restricted to Noetherian bases and cannot alone
be instantiated for this statement's arbitrary affine base and arbitrary base change.
The existing arbitrary-base projective-line exchange has exactly the required generality.
No mathematical statement or target has been weakened.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
