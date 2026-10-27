## What changed

Restored the archived proof of
`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` in
`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`.
The proof follows the existing node
`lem-sf-adic-affine-direct-image-finiteness`: affine embedding, dense open into
the scheme-theoretic image, closed image inclusion, projective projection, and
derived composition. The node now cites the standard affine-chart lemma actually used instead of
the unused packaged affine compactification; the mathematical route is unchanged.

Removed the unused private proof imports from
`Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` and
`Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness`. These modules retain
their original public imports, signatures, docstrings, and `sorry` bodies.
This makes the existing input lemmas available below LowerStar without the
ScalarExtension/PointPerfect/DerivedForget import cycle. The closed-immersion
input already lies below LowerStar and needs no change.

Change record: `coord/changes/Z7-adic-lower-star-acyclic-finiteness.md`.
The source graph with the three delivered files overlaid has zero cycles.

Searches: `msearch.py` LeanFinder for derived pushforward of constructible adic
sheaves between affine schemes found algebraic-geometric finite-type results,
but no replacement for the adic finiteness theorem. Loogle for `finiteLowerStar`
found no Mathlib declaration. A source search for the affine theorem and the
three bounded-constructibility inputs confirmed the existing declarations.

## Proved and sorry left

Closed one of the item's one holes:
`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`
(`lem-sf-adic-affine-direct-image-finiteness`). No holes remain in the item.
No new holes or split-off theorems are added.

The two adapted input modules retain these existing holes:

- `AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_of_denseOpenImmersion`
  (`lem-sf-adic-dense-open-direct-image-finiteness`).
- `AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_projectiveSpace`
  (`lem-sf-adic-projective-space-direct-image-finiteness`).

Thus the affine theorem is proved from the previously stated input lemmas; its
transitive proof still depends on their existing holes. The closed-immersion
input already has a complete proof and is preserved.

## No longer needed

Removed from the dense-open input's private imports:

- `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.LisseEConstructibleIntegralLattice`
- `Sheaf.Paper.SfIntegralDirectImageConstructible`

Removed from the projective-space input's private imports:

- `Sheaf.AlgebraicGeometry.ProperBoundedConstructible`
- `Sheaf.AlgebraicGeometry.ProperCaseConstructibility`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.LisseEConstructibleIntegralLattice`
- `Sheaf.Paper.SfIntegralDirectImageConstructible`

These imports serve neither current statements nor current proof bodies. Their
mathematical statements remain dependencies of the two unfinished input lemmas;
none of their own DAG edges or declarations is withdrawn. No module is claimed to
leave the targets' entire closure merely because these edges are removed.

All three existing adic finiteness input modules are used by the restored proof.
The existing DAG plan names `def-nagata-affine-compactification`, whose packaged
compactification declaration is not used: the proof constructs its affine chart
and image factorization directly. The affine node's proof dependencies replace this unused node with
`lemma-nagata-relative-affine-space-open-immersion`, which supplies the chart
actually used. This is the archived proof's existing route, with no unit step
bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier proof's mathematical composition was valid, but unused private
imports of its two unfinished input modules became cyclic after upstream added
the PointPerfect-to-LowerStar path. Removing those unused imports suffices;
moving or duplicating the input declarations is unnecessary.
The finite-torsion unit route and the affine adic compactification argument are
preserved. No source statement or definition is changed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
