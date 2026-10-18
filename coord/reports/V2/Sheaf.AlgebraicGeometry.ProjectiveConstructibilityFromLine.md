## What changed

Proved `AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_projectiveLine`
in `Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine`, with its signature and
both public imports unchanged. Only this Lean module and its existing node's proof fields
are changed. No definitions, statements, consumer files, or target declarations are changed.

The proof uses the existing source-library `projectiveLinePow` tower and
`exists_isFinite_surjective_projectiveLinePow`, proves constructibility of its projection
by induction from the supplied projective-line hypothesis and the existing composition
lemma, applies the existing finite-surjection cancellation lemma, and composes with the
closed projective embedding. Two fully proved private helpers handle coefficient pullback
and closed immersions. The latter uses closed-pushforward constructibility, the finite-value
constructibility comparison, finite-pushforward exactness, and the existing bounded-below
derived comparison. The proof covers empty coordinate types by the empty-source closed
immersion instance; the source cover includes the one-coordinate, dimension-zero case.

Compilation through `lcompile.py` passes without errors or warnings after pruning (14.9 s).
The import direction check for the source symmetric-product module passes. The unit record
`sk-prop-sf-cbc` has no realized statement/steps to bypass, and the proof preserves the
blueprint's projective embedding, projective-line tower, symmetric-cover cancellation,
and closed-composition route. Both the master and main-20261015 proof texts were read.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_projectiveLine`
(node `lem-finrepair-projective-from-line`). Added 0 holes. There is no `sorry` left in
any delivered Lean file, and no split-off module or theorem. Both private helpers are proved.
This is a proof from existing declared dependencies, not a decomposition. The already
stated composition and finite-surjection cancellation theorems remain dependencies;
this delivery does not claim to discharge their existing holes.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`.
- `Sheaf.AlgebraicGeometry.NoetherianSymmetricProductFiniteSurjective`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` (already supplied by the unchanged
  public projectivity import).
- `WeilConjectures.ConstructibleSheaf.OpenClosed` (supplied by the more specific
  `WeilConjectures.ConstructibleSheaf.ExtensionByZero` proof import).

The proof no longer uses `def-nagata-relative-projective-space`, its module
`Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`, or any comparison with relative Proj.
It no longer needs the separately constructed product cone from `def-pc-fibre-product`.
It no longer uses `lem-fin-symmetric-product-finite` or its module
`Sheaf.AlgebraicGeometry.NoetherianSymmetricProductFiniteSurjective`: the existing
source-library symmetric-product cover works on the recursive tower, over any base,
with arbitrary finite nonempty coordinate types. Its finite and surjective clauses
are recorded under `lem-weil-pbc-symmetric-product-finite` and
`lem-weil-pbc-symmetric-product-surjective`. No separate Noetherian-base check is needed
for that cover. Local Noetherianity is still used for the closed-immersion helper.

The proof does not use the bounded-derived-category definitions of
`def-weil-pbc-constructible-complexes`; zero constructibility comes directly from
`Scheme.IsConstructibleSheaf.of_isZero` and the constructibility comparison.
The removed bounded-constructible imports were redundant with the statement imports;
no claim is made that these modules leave every target's import closure.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof used relative-Proj charts and a separate comparison of products
with recursive bundles. Those steps are unnecessary because the source library already
constructs the exact recursive tower and provides its finite surjective cover. The old
node/module docstring also omitted the empty coordinate type allowed by `IsHProjective`;
the Lean proof now handles it explicitly without changing the statement.

The recorded closed-immersion declaration alone is an underived, source-constructibility
statement with an open-complement argument. The proof uses its existing
`lowerStar_of_isClosedImmersion_of_quasiCompact` wrapper, obtains quasi-compactness from
local Noetherianity, converts the constructibility predicates using the upstream
`isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`, and supplies higher vanishing
using finite-pushforward exactness and the bounded-below exact-functor comparison.
These are existing interfaces, not new assumptions.

Existing results used as tools from other units are projective-space properness,
source-library symmetric-product finiteness/surjectivity, the constructibility-predicate
comparison, closed-immersion finiteness, and finite-pushforward exactness. They implement
individual steps of the original route; no unit statement or proof step is bypassed.
No maintainer `tool_uses` approval fields were added or modified.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
