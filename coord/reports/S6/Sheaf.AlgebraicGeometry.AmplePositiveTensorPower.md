## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isAmple_positive_tensorPow` in
`Sheaf.AlgebraicGeometry.AmplePositiveTensorPower`, with its signature unchanged.
The proof powers each ample section and transports it through the two tensor-power
multiplication isomorphisms and commutativity of multiplication. The existing proved
`compl_support_zeroLocus_tensorPowSection` and
`nonvanishingLocus_eq_compl_support_zeroLocus` identify its nonvanishing locus with the
original affine open. A proved private evaluation-at-one helper supplies the section/morphism
round trip. Compactness and the original positive exponent are retained.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.AffineComplement`; changed the zero-locus comparison
import from `import all` to ordinary proof-only `import`. The two existing public imports
remain because the signature needs ampleness, tensor powers, and their invertibility instance.
Updated the item's node proof, proof dependencies, and proof origin to match this route.

The launcher single-file compilation passed without warnings (3.6 seconds). Checked both new
proof dependencies with `tools/import_direction.py`: neither creates an import cycle.
The source, Properties Lemma 01PT, proves the result precisely by equality of the powered
section's nonvanishing locus. Empty schemes need no separate assumption; positivity of k
is used in the existing power theorem. LeanFinder found basic-open power results, Loogle
found `isUnit_pow_iff`, and Mathlib grep found no exact ampleness theorem; the source library's
existing zero-locus power result supplies the shorter proof.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.isAmple_positive_tensorPow`
(node `lem-sc-ample-positive-tensor-power`).
No holes remain in the item; no holes or public statements were added anywhere.
This is a proof, not a decomposition.

## No longer needed

Removed direct imports:
- `Sheaf.AlgebraicGeometry.AmpleIso` (previously `import all`): no ampleness-isomorphism theorem
  or private stalk-isomorphism helper is used. The route does not need node `lem-sc-ample-iso`.
- `WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`: its tensor-power section
  declarations are already supplied by the necessary `Modules.AffineComplement` import;
  this module remains a transitive dependency, so it is not globally pruned.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: already supplied by the public
  imports and remains necessary transitively.

Removed the unused private `nonvanishing_of_frame` and the old direct stalk/frame argument.
The revised DAG needs no new lemmas for bijectivity on stalks, maximal-ideal membership,
positive-power units, or transport on stalks: the existing proved zero-locus theorems
perform that work. No original declared proof dependency was dropped: both definition nodes
remain used. No claim is made that any removed direct import is unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The original node plan repeated local calculations already proved by the source library.
Its proof-origin note claimed an H2 formal proof, whereas the assigned theorem still had
its original `sorry`; the delivery replaces that note with the actual proof route.
The current Stacks source's label is `lemma-ample-power-ample` rather than `lemma-ample-power`;
the tag and mathematical result agree. There were no statement or definition changes,
no new nodes, and no adaptations of other groups' files.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
