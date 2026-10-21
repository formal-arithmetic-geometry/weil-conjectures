## What changed

Restored Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare from the
quarantine path recorded in coord/rework.tsv. Qualified every intended derived
pullback as AlgebraicGeometry.derivedPullback, repairing actual elaboration
errors caused by the newer Scheme.Modules.derivedPullback shadowing that name.
The original mathematical theorem, binders, universes, assumptions and canonical
maps remain. canonicalDirectImageH0Iso and its body are unchanged. Updated only
the node's Lean statement and restoration metadata; the proof plan is retained.

The complete archived argument is preserved. The private canonicalSingleMateSquare
uses the pinned adjunction transpose at the ordinary counit, naturality of the
derived composition comparison, and canonicalSinglePullbackSquare. Applying H0,
single-homology naturality and canonicalDirectImageH0Unit gives the public square.
No flatness, cartesian, invertibility or extra vanishing assumption is added.

Change record: coord/changes/E4-canonical-degree-zero-mate-square-restoration.md.
No source-library modules, targets, other group's modules or unit routes change.

## Proved and sorry left

Zero-hole repair: the archive contained 0 sorries and the restored module has
0 sorries. Holes closed: none. Holes added: none. Split off: none.
AlgebraicGeometry.Scheme.Modules.canonicalDegreeZeroMateSquare and the four private
helpers transposeCounit, counitOfTranspose, transposeComposite and
canonicalSingleMateSquare retain complete proofs. canonicalDirectImageH0Iso is
the original explicit composition of the unbounded single-object homology
comparison and rightDerivedZeroIsoSelf, with no postponed data.

The unmodified archive failed with Type u versus Type w morphism mismatches at
lines 88 and 231. The qualified implementation compiled in 44.2 seconds; its
line-width warnings were then fixed. The final pruned source compiled cleanly in 42.1 seconds. The delivery tool
checks the axioms of every declaration. All actual consumers
are quarantined; their intended signatures and dependencies are preserved.

## No longer needed

Removed private imports:

- Sheaf.AlgebraicGeometry.DerivedPullbackComposition: retired empty compatibility
  module; the retained public base-change import supplies the adopted source API.
- WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage: redundant direct
  import; already public through CanonicalSingleDirectImageComparison.
- WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction: redundant direct
  import; already public through SchemeDerivedBaseChangeMap and its composition API.

No mathematical dependency, DAG node, source declaration, or parent route is
pruned. Every listed proof dependency remains used by the complete argument.
All five original public imports and all three compatibility proof imports remain.
No new module or node is added.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined and already had a complete zero-hole proof; the work is
restoration against the adopted source API. Unqualified derivedPullback inside
Scheme.Modules no longer denotes the shared-category functor used by the pinned
single-module comparisons. Explicit qualification restores that intended type.
The proof plan is correct and needs no new split or mathematical repair.

The search services returned generic adjunction naturality and unrelated homology
lemmas, not a shorter scheme-specific mate square. The archived proof already
uses the three existing compatibility results. No withdrawal is justified by the
absence of live consumers: its quarantined parents and their DAG dependencies
still require the theorem and its canonical H0 comparison.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
