## What changed

Proved `AlgebraicGeometry.affine_groupoid_polynomial_norm_invariant` in
`Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant`, with its statement,
existing docstrings and public imports unchanged. The proof follows the three steps of
`lem-a1-affine-groupoid-polynomial-norm-invariant`; no route or dependency changed.

Private constructions identify maps to `Spec A[T]` by their projection to `Spec A`
and the image of `T`, using the Gamma-Spec adjunction and polynomial evaluation.
The polynomial source and target maps are finite locally free: the polynomial algebra
pushout gives their base-change squares, and the finite, flat and locally finitely
presented properties each pull back.

The test-point groupoids give all fields of `Scheme.IsGroupoid`: identities, inverse,
composition and associativity are transported through the supplied arrow equivalences.
The polynomial composition is constructed from the composition of the base arrows and
the shared polynomial coordinate. Checking the base projection and coordinate proves
all its groupoid laws. Applying `affineGroupoid_invariant_norm` to these polynomial
rings and `F`, `Q`, `hQ` gives precisely the asserted equality of polynomial maps.

Read Stacks `groupoids.tex`, `lemma-determinant-trick` (03BH) and the second paragraph
of `lemma-integral-over-invariants`, and `exercises.tex`, `exercise-trace-det-rings`
(02DV), including its base-change assertion. LeanFinder, Loogle and grep searches found
no shorter ready-made polynomial groupoid invariance theorem. No constant-rank,
nonempty-source, reducedness or global-freeness assumption enters the proof.

Validation: the complete module compiled through `lcompile.py` in 19.4 seconds with
no errors or warnings. Its original theorem signature was compared verbatim, and
all lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.affine_groupoid_polynomial_norm_invariant`
(node `lem-a1-affine-groupoid-polynomial-norm-invariant`).

No `sorry` remains in the delivered module. Added 0 holes and split off 0 statements.
All private helpers are proved, and all private data constructions are explicit.
The existing dependency `AlgebraicGeometry.affineGroupoid_invariant_norm`
(node `lem-a1-affine-groupoid-invariant-norm`) remains sorried in its own unchanged
module; this delivery proves the assigned theorem from that declared dependency.

## No longer needed

None. No original imports, declared dependencies, nodes or modules were pruned.
The proof continues to use `Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm`.
No additional import was retained.

## Where the brief, the DAG or earlier work was wrong

The dependency now takes explicit `Scheme.IsGroupoid` laws, whereas the assigned
theorem supplies equivalences to test-point groupoids. The proved private conversion
handles this interface difference without changing either statement. The polynomial
base-change construction is fully proved rather than left implicit in step 1.
No mathematical statement error or unit-route change was found.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
