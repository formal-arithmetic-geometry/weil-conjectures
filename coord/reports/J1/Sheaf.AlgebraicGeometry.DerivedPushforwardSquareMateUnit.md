## What changed

Repaired `Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit` by replacing its
restored duplicate implementation with a compatibility import of
`WeilConjectures.AlgebraicGeometry.DerivedPushforwardSquareMateUnit`. The adopted source
already contains the identical statement and complete proof of
`AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit`. The old and adopted theorem
signatures were compared byte for byte and are identical. The existing public import of
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` is preserved.

Updated the Lean attachment of `lem-pc-derived-pushforward-square-mate-unit` to the
adopted source module. Its mathematical statement, proof plan, proof dependencies and
unit route are preserved. No source-library file is modified. The change record is
`coord/changes/DerivedPushforwardSquareMateUnit-source-compatibility-J1.md`.

Validation: the restored implementation compiled in 51.6 seconds; the compatibility
module compiled in 3.5 seconds. An additional consumer imports both module paths and
applies the re-exported theorem to the exact former statement, checking both compatibility
and absence of duplicate declarations; both files compiled successfully (2.8 and 10.0
seconds). `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The read-only import-direction check permits the
new import. The downstream search found zero current importers of the Sheaf module;
the existing source consumer already imports the adopted module and needs no adaptation.

## Proved and sorry left

This is a zero-hole repair: zero holes before, zero holes after, zero holes closed,
and zero holes added. There are no `sorry` declarations in the delivered module.
`AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit` retains its complete proof
in the adopted source module. No statements are split off and no new nodes are added.

## No longer needed

Removed the duplicate private implementations `square_paste`, `normalized_unit`,
`canonical_adjoint_eq`, and `canonical_conjugate_eq` from the Sheaf compatibility file.
The corresponding complete helpers remain unchanged in the adopted source proof.
Removed the Sheaf file's private imports
`WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport` and
`WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate`; the adopted source
still imports and uses both. No mathematical dependency node or module is pruned:
`lem-pc-direct-image-square-unit-transport`, `lem-sc-derived-direct-image-square-mate`,
and `lem-pc-ringed-spaces-derived-direct-image-composition` remain necessary.
The compatibility module itself is retained, with its public import contract preserved.

## Where the brief, the DAG or earlier work was wrong

The stale rework row refers to the earlier cluster-restoration build failure. The current
Sheaf implementation already includes P4's removal of the redundant `derivedPullback`
irreducibility attribute and compiles. Re-delivering that change would be a no-op.
The current adopted source additionally supplies the same public declaration with the
same proof. Keeping a second implementation in Sheaf risks a duplicate declaration when
the two import closures meet and repeats an expensive elaboration. The delivered repair
uses the existing adopted declaration and corrects the stale Lean attachment rather than
changing its mathematics or discarding the quarantined theorem and dependencies.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
