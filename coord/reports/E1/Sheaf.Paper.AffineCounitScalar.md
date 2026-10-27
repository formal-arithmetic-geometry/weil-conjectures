## What changed

`Sheaf.Paper.AffineCounitScalar` now proves the stated equation by induction on the
ordered coordinate tower and transport to the specified compactification. The existing
`affineScalarCompactificationCounit` definition and the theorem signature are preserved.
The private categorical induction uses the actual composite adjunction counits. The
private domain lemma transports the supplied chart-domain result through the ordered
right normal form. The coefficient-map normalization identifies the published map with
`compactScalarMap`.

Two separate comparison results are stated in their own modules: the canonical scalar
counit equation for one affine coordinate, and equality of the recursive ambient left
comparison with the bounded-below compactification comparison. Their docstrings and
nodes give the source and complete arguments. The main proof combines them by actual
naturality equations and cancellation of the comparison isomorphism.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.affine_counit_scalar` (the item's one original hole).
The item module has zero remaining holes.

Added and remaining:
- `AlgebraicGeometry.Etale.affineLineCanonicalScalarCounit`
  (`lem-sp-affine-line-canonical-scalar-counit`).
- `AlgebraicGeometry.Etale.affineCompactificationComparison_normalization`
  (`lem-sp-affine-compactification-normalization`).

This is a decomposition: one upper hole closed, two separate lower holes added; it is
not a claim of a net reduction in holes. Both are strictly part of the argument: one
is the single-coordinate geometric calculation, the other a scalar-free comparison
normalization for arbitrary bounded-below inputs. There is no sorry in a definition
or private declaration. The private tower induction and final transport calculation
are complete Lean proofs.

## No longer needed

- `lem-sp-finite-tower-scalar-mates` / `Sheaf.CategoryTheory.FiniteTowerScalarMates`:
  the direct induction uses the library's recursive tower, including the identity base
  case, without a separate finite-tower presentation.
- `lem-sp-ordered-tate-scalar-normalization` /
  `Sheaf.Paper.OrderedTateScalarNormalization`: the theorem already uses the ordered
  recursive right comparison; the generic right exchange equals that map by coordinate induction.
- `lem-sp-affine-line-scalar-mates` / `Sheaf.Paper.AffineLineScalarMates` is not imported
  by this route. Its sum-extension interface would require additional comparisons;
  the new line constituent uses the already specified open/projective adjunction and
  root-normalized reduction map directly. Its existing attachment is not withdrawn.

The new line statement omits unused proof imports of `Sheaf.Paper.P1CounitScalar`
and `Sheaf.Paper.ProperOpenCoefficientRefinement`; its proof plan still records the
needed projective and open comparison results.

No existing Lean module is deleted. The original public imports are retained. No
whole-library pruning is asserted for nodes that may have other parents.

## Where the brief, the DAG or earlier work was wrong

The original dependency `Sheaf.Paper.AffineLineScalarMates` has a DAG attachment and a
stage-2 report but no current source file, and it has no rework row. Its reported
statement also uses a sum-extension presentation and asserts additional clauses. This
packet preserves that record and introduces a distinctly named open/projective
constituent; it does not silently replace the old theorem by a weaker statement.

The ordered compactification square is stated using a bounded-below comparison,
whereas the item's counit definition uses an ambient recursive comparison. Their
normalization equality is needed and was not a separately attached dependency in the
original plan. The new node records it explicitly. The source-library tree is untouched.

Edge cases: all statements include d=0, empty schemes, zero inputs, zero coefficient
rings and n=0 (which forces the coefficient rings to be zero). No flatness or finite
projective-dimension assumption is added. All compactification comparisons are the
specified constructions. Bounded-below use is confined to ctf inputs and their stated
scalar extensions.

## New nodes

`lem-sp-affine-line-canonical-scalar-counit` states the actual single-coordinate
open/projective scalar counit equation with `reductionEtaleLineScalarIso`, from the
Charts argument, open mate normalization and projective-line scalar counit.

`lem-sp-affine-compactification-normalization` states the bounded restriction of the
recursive affine comparison, from identity, pairwise and composition compatibility
of bounded and unbounded compact support. Its source is the normalization step in
Charts and the existing compact-support comparison theorem.

`def-sp-affine-counit-comparison-objects` records definition-only ownership of the
already constructed scalar and left comparisons in `ReductionExceptional`. This avoids
a dependency back to the parent reduction theorem; no declaration or signature changes.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
