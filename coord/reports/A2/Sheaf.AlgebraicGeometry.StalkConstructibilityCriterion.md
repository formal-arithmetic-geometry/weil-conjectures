## What changed

Proved the converse in `Sheaf.AlgebraicGeometry.StalkConstructibilityCriterion` without
changing either public theorem signature, any public import, or any definition.
The private proof helpers implement finite generic-stalk section lifting (including the
addition table), generic injectivity, a locally bijective constant-presheaf map, its
sheafification to a constant chart, and Noetherian induction with open/closed gluing.
The existing forward implication is retained.

The induction uses Mathlib's concrete vanishing-ideal closed subscheme. The constant
chart is obtained with the locally bijective sheafification criterion rather than a
geometric-stalk conservativity theorem. The two node proof records and the main
theorem's proof docstring now describe these actual constructions.

Added proof imports:
- `WeilConjectures.AlgebraicGeometry.Sites.PointFunctions`
- `WeilConjectures.Mathlib.Topology.Constructible`

Validation: the complete module compiles through lcompile.py, with no errors or
warnings, after removing the unused imports. The edge cases are handled explicitly:
the empty scheme has an empty etale cover; a finite abelian stalk is nonempty, so its
cardinality is positive; the generic neighbourhood retains its marked point after
intersection with the constant-cardinality open. Delivery preflight checks compilation,
public signatures, forbidden declarations and axiom dependencies independently.

## Proved and sorry left

Closed 1 of 1 original holes:
- `AlgebraicGeometry.Scheme.isConstructibleAbelianSheaf_of_constructible_stalk_cardinality_loci`
  (`fin4-lem-stalk-constructibility-criterion-converse`).

The public equivalence
`AlgebraicGeometry.Scheme.isConstructibleAbelianSheaf_iff_constructible_stalk_cardinality_loci`
now uses the completed converse. All ten added private helpers are proved. Added holes: 0.
Remaining holes in the delivered module: 0. No split-off modules or new nodes.

## No longer needed

Removed these ten direct proof imports (some are still available transitively):
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Pruned these nodes from the criterion's proof dependencies:
- `lem-weil-pbc-reduced-induced-closed-subscheme`: the induction needs a closed
  complement with known range, constructed by Mathlib's vanishing ideal; no reducedness
  assertion or existential subscheme wrapper is used.
- `lemma-weil-pbc-geometric-stalk-conservative`: local injectivity and local surjectivity
  of the concrete presheaf map directly imply that its sheafification is an isomorphism.
- `lem-weil-pbc-inverse-image-stalk-germ`: only the source-library stalk comparison
  isomorphism `upperStarCompSheafFiberIso` is needed. Germs in the construction all live
  on the original site and use the Point API's restriction naturality.
- `lem-weil-pbc-affine-etale-essentially-small-cover`: the existing Point elementwise
  APIs already handle the small colimit model; this proof constructs no affine skeleton.

The three non-leaf wrapper modules corresponding to the reduced-subscheme and
inverse-image-stalk-germ nodes are no longer direct dependencies. The constant-stalk
wrapper module is also unnecessary; the proved general Point constant-sheaf isomorphism
is used. No global unreachability of a module from other targets is asserted.

The proof records now explicitly cite `lemma-openclosed-stalk-upperstar`,
`lem-weil-pbc-geometric-stalk-comparison-constant`, and `prop-constructible-open-closed`,
whose existing declarations are actually used; no new statement was introduced.

## Where the brief, the DAG or earlier work was wrong

The converse node previously cited the main criterion as its sole proof dependency,
although the main criterion already applied that converse. Replaced this circular
proof placeholder with the six concrete stages of the implemented converse.
The original plan's reduced-subscheme and inverse-image-unit compatibility obligations
were stronger than this proof needs; the replacements above preserve the statements.
The full plan is implemented, including generic finite-table lifting and Noetherian
induction; no blueprint-unit step is bypassed.

A shorter-route search found the source library's finite-ring module-sheaf criterion,
but arbitrary finite abelian stalks do not supply a global finite coefficient ring.
The present argument therefore implements the abelian finite-table route. Mathlib
searches via leanfinder, loogle and grep found no direct replacement theorem.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
