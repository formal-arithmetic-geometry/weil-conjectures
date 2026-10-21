## What changed

Restored the full quarantined implementation of
Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare, retaining its theorem,
all seven imports, pinned derived counits, flatness argument, exchange square,
and homology/naturality cancellation proof. Qualified the three occurrences of
derivedPullback in the statement and the corresponding proof occurrence as
AlgebraicGeometry.derivedPullback.{u, w}. This restores the intended functor on the
shared derived categories after the adopted source introduced the different
Scheme.Modules.derivedPullback. No hypothesis, canonical map or conclusion changes.

Refreshed only the existing node's Lean statement and restoration metadata; its
statement/proof dependencies, four proof steps and unit route are preserved.
The change record is coord/changes/P2-tensor-degree-zero-mate-square-restoration.md.
There are no new nodes, auxiliary statements, definition changes or adaptations.

The original archive was compiled against the current dependency interface and
fails at lines 71 and 73: DerivedCategory.{w, u, u + 1} is supplied where the newer
namespace-local functor expects DerivedCategory.{u, u, u + 1}. The restored proof
compiles with the intended arbitrary universe w. Its two original long lines were
wrapped after qualification to retain the 100-character limit.

The downstream query cannot index the absent item. An import scan of both live
and quarantined sources found the one direct consumer,
PicardRankMatchDerivedTruncationData, and eighteen transitive consumers. They
remain quarantined rework assignments. The direct consumer uses the same pinned
comparison and shared derived categories; no consumer is weakened or withdrawn.

## Proved and sorry left

This is a zero-hole restoration, not a new hole closure:
AlgebraicGeometry.Scheme.Modules.tensorDegreeZeroMateSquare had zero sorries in
its archive and has zero sorries in the restored module. Holes closed: none.
Holes added: none. Sorries left: none. No result is split off.

Validation: the restored file compiles without errors or warnings in 26.5 seconds.
#print axioms reports exactly propext, Classical.choice and Quot.sound. An
unchanged copy of the recently restored CanonicalDegreeZeroMateSquare was
compiled for local validation because the published cache initially mixed its
old Sheaf base-change declaration with the adopted source declaration. That
identical dependency source is not part of this delivery.

The complete original argument is retained: construct phi from derived base
change and the pinned pullback comparison, prove the finite locally free source
comparison invertible using affine projective sections, apply
TensorSingleBaseChangeSquare, then take H0 and use canonicalDirectImageH0Unit
and naturality. The inverse cancellation concerns only the source comparison;
phi and the ordinary base-change map are never assumed invertible. No new
statement or edge case is introduced: the same proof covers rank zero, the zero
module, and empty schemes.

## No longer needed

None. No imports, dependency nodes, modules or declarations are pruned. In
particular, preserve lem-sc-picard-tensor-degree-zero-mate-square and its parent
lem-sc-picard-rank-match-derived-truncation-data. Zero live Lean importers does
not make this quarantined dependency unnecessary. Every public import supports
the signature; all four private imports are used by the proof.

LeanFinder found only unrelated differential/cotangent tensor-base-change
results; Loogle found singleFunctorCompHomologyFunctorIso, which the retained
proof already uses; repository and Mathlib text search found the existing
flat-comparison and degree-zero-unit ingredients, with no shorter replacement
for the complete canonical tensor mate square. No new proof route is needed.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because it was quarantined by the
upstream-sync recovery, not withdrawn. Its archive already contains a complete
zero-hole proof. The defect is the adopted source's new namespace-local
DerivedCategory pullback shadowing the pinned arbitrary-universe functor. The
restoration repairs that name resolution, without handing the obligation to a
new lemma or changing the node's mathematical statement.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
