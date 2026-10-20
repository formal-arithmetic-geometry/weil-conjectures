## What changed

Proved `AlgebraicGeometry.Etale.relativeConeSupportComparison` in
`lean/Sheaf/AlgebraicGeometry/PurityRelativeCone.lean`. The original public definitions,
structures, theorem signature and public imports are preserved verbatim. Private helpers
construct the supported-complex kernel isomorphism, its normalized cone realization, the
single-site systems and every field of the change-of-topology comparison.

The topology argument transposes an augmented resolution lift through the comparison
adjunction. Acyclicity of the pulled-back injective terms makes this transposed lift a
quasi-isomorphism. Its source and target have injective terms, so it is a homotopy
equivalence. Applying evaluation or supported sections preserves the equivalence. Kernel
coordinates then give the cone comparison and all its naturality equations.

Added `lean/Sheaf/Algebra/Homology/KernelShiftedConeBoundary.lean`, containing the proved
general theorem `CochainComplex.kernelShiftedCone_boundary`. It identifies the shifted
cone inclusion with the connecting map of the kernel short exact sequence, with the
actual shift signs. The proof is a cycle-lifting argument with epimorphic refinements
in an arbitrary abelian category.

Updated the original DAG node's proof, proof dependencies and proof origin to this
argument. Removed obsolete approved tool uses without adding or reordering approvals.
Private kernel-limit, homotopy and kernel-to-cone isomorphism constructions are
irreducible so that subsequent proofs use their interfaces. Explicit complex arguments
avoid inferring a complex from its kernel. Supported coefficient maps are compared
before extension by zero, avoiding reduction of whole extended kernel constructions.

The final `lcompile.py --all` check compiled both modules cleanly; the item took
53.7 seconds, within the unchanged 60-second limit. Public declarations and the item
theorem signature were compared with the shared source and are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.relativeConeSupportComparison`
(node `lem-pur-divisor-relative-cone`): 1 of 1 original holes closed.

The new theorem `CochainComplex.kernelShiftedCone_boundary`
(node `lem-pur-kernel-shifted-cone-boundary`) is also fully proved.

No `sorry` remains in either delivered Lean module. Holes added: 0. Unproved statements
split off: 0. This is a proof from existing declared dependencies, not a decomposition
into new holes.

## No longer needed

Removed these private imports from the item module:

- `Mathlib.Algebra.Homology.HomologySequenceLemmas`.
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`.
- `Sheaf.CategoryTheory.SiteCohomologyPullback`.
- `Sheaf.CategoryTheory.SiteLerayDegenerate`.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
  (redundant: the needed acyclic-resolution API imports it).

The proof no longer uses the following declared mathematical dependencies directly:
`lem-cbc-abelian-etale-proetale-cohomology-comparison`,
`lem-cbc-comparison-pullback-sections`,
`lem-weil-pbc-site-cohomology-pullback`,
`lem-weil-pbc-site-leray-degenerate`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-complex-ses-long-exact-naturality`, and
`lem-weil-pbc-five-lemma`. The generic Grothendieck comparison-unit theorem and the
already-proved exactness instances replace the site-pullback/Leray-edge route; the
supported-section homotopy equivalence replaces the five-lemma route. The direct
`def-weil-pbc-sites-and-cohomology` proof edge is also unnecessary.

`lem-weil-pbc-complex-ses-homology-long-exact` is retained through the new boundary
lemma, rather than as a direct edge of the item. The comparison-pullback-section node
may remain a dependency of the existing Grothendieck-unit theorem. No source-library
declaration or module is withdrawn, and no global pruning of those surviving uses is
claimed. The five obsolete approved tool uses removed from the original node are the
abelian cohomology comparison, site cohomology pullback, abelian pullback exactness,
comparison pullback sections, and site Leray degeneration entries.

## Where the brief, the DAG or earlier work was wrong

No statement was false and no definition or target signature needed repair. The stated
proof plan was longer than necessary: the source library already provides the generic
Grothendieck unit isomorphism, the degreewise-epimorphic kernel/cone comparison and the
acyclic quasi-isomorphism comparison API. Using these avoids the object-level Leray-edge
and five-lemma detours. The boundary-sign compatibility still required an explicit
argument; it is now proved in its own general module. The blueprint unit statement and
its realized route are unchanged.

## New nodes

`lem-pur-kernel-shifted-cone-boundary`, in
`dag/nodes/sec-smooth-purity/lem-pur-kernel-shifted-cone-boundary.json`, records the general
boundary equality needed in Step 3 of the original plan. Its complete proof is in
`CochainComplex.kernelShiftedCone_boundary`. The statement applies to all integer degrees
and arbitrary abelian categories; the proof handles negative degrees and degree zero
without boundedness assumptions. Its source is the Stacks connecting-map cycle formula
and cone construction. LeanSearch, Loogle/LeanFinder and source grep found no exact existing theorem.
No change record is required because existing public statements and definitions are
unchanged.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
