## What changed

Proved `AlgebraicGeometry.ProEtale.VectorIntegrationSite.infinityCartier` in
`Sheaf.Paper.ProEtaleAffineLineCounit`, without changing its signature or any definition.
Added private proof imports of
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth` and
`WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier`.

The infinity section is closed because its composite with the separated projective-line
projection is the identity. Its canonical map to its scheme-theoretic image is an isomorphism.
Cancelling that map in the section equation identifies the closed subscheme's projection
with its inverse. The latter is finite, flat and locally of finite presentation. The proved
smooth-relative-dimension-one instance and the existing Cartier criterion conclude the proof.
This works over every base, including the empty scheme and nonreduced bases.

Updated the existing node's proof, proof_deps and proof_origin to record this route.
The external node `lem-pc-cartier-criterion` is used as a generic, already proved tool,
not as a replacement of a smooth-purity unit step. The unit's realized routes are unchanged.
No definitions, statements or source-library files were modified.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.infinityCartier`
(node `def-pur-proetale-affine-line-counit`).
No sorry remains in the item; no holes were added or split off.
The two added source-library proof imports contain no sorry.
The server single-file compile succeeds; the initial unused simp-argument warning was removed.
Delivery performs the final compile and preflight checks.

## No longer needed

No imports, nodes or modules were removed or withdrawn. The coordinate-gluing argument in
the existing theorem docstring need not be separately formalized: the already proved
Cartier criterion supplies the shorter argument. The original node had no proof dependencies,
so none were pruned. The existing public import remains needed by the definitions.

## Where the brief, the DAG or earlier work was wrong

No mathematical or tool error was found. The node is a definition node with no recorded proof
steps, but its Lean module also contains the named theorem infinityCartier; the route update
now records its proof. The saved searches (LeanFinder, Loogle and grep) found no exact Mathlib
result. Project searches found the proved source-library Cartier criterion and relative
projective-line smoothness, which are reused directly. No new nodes were needed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
