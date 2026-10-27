## What changed

Replaced the sole hole in
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_hom_lift`
by a complete proof from existing Picard H1 generator lifting and one new geometry
statement. The theorem's signature and all existing public imports are unchanged.
The proof imports ProjectiveBundleFiberGeometry,
PicardH1LocalSectionBaseDescentGenerator, ProperFlatGlobalSections,
ProjectiveBundleProper, Modules.Dual, and ModulePullbackTensor privately.

For L = M dual tensor N, the given fibre isomorphism and pulled-back dual
evaluation trivialize the fibre of L. The Picard generator theorem is applied
with Fin 0: all comparison-family conditions are vacuous, and H1(O)=0 proves the
injectivity hypothesis. A proved private helper removes the proper image of
the nongenerating locus and retains the actual unit trivialization. Explicit
pullback comparisons identify this with a trivialization on the inverse-image
open. Tensor cancellation then constructs an isomorphism M|U ≅ N|U; its hom
satisfies the requested fibre condition by functoriality. These constructions,
the proper shrinking argument, and all comparison isomorphisms are proved here.
No arbitrary data is defined by choosing from an unproved existence theorem.

Added ProjectiveBundleFiberGeometry and its node. Updated only proof,
proof_deps and proof_origin of the assigned node to record this route.
No existing shared interface, source-library declaration, or target changed.

## Proved and sorry left

Closed one of the item's one original holes:
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_hom_lift`
(node `lem-sfb-projective-bundle-fiber-hom-lift`). The assigned module has zero
remaining holes. All four private helpers are proved.

Added one hole:
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_geometry`
(node `lem-sfb-projective-bundle-fiber-geometry`, new module
`Sheaf.AlgebraicGeometry.ProjectiveBundleFiberGeometry`). It asserts flatness,
local finite presentation, geometric reducedness and connectedness of fibres,
and H1(O)=0 for the positive-rank canonical projective bundle. It says nothing
about M, N, their fibre isomorphism, a neighbourhood, sections, or lifting maps.
It is the geometry step of the original plan, not the original lifting
obligation under another name. Its docstring gives the polynomial-chart and
projective-space cohomology proof, including rank one and the empty base.

This delivery is a decomposition: one upper hole closed, one strictly smaller
geometry hole added, net zero holes closed. It also uses previously stated
proof dependencies that may themselves still have holes; none is restated or
modified. The compile results and delivery preflight are the validation.

## No longer needed

The assigned file originally imported only its statement dependencies. All
those public imports stay; no original Lean import was removed. No module is
withdrawn and no global pruning is claimed.

The new proof avoids the original separate Noetherian approximation argument.
These nodes/modules are no longer direct dependencies of this item's proof:

- `lem-sfb-proper-flat-fibre-section-lifting` /
  `Sheaf.AlgebraicGeometry.ProperFlatFibreSectionLifting`;
- `lemma-nagata-noetherian-inverse-system-affine` /
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`;
- `lem-weil-pbc-finite-type-over-noetherian` (Mathlib leaf);
- `lem-weil-pbc-limit-fibre-products` /
  `WeilConjectures.AlgebraicGeometry.LimitFibreProducts`;
- `lem-trf-invertible-affine-limit-descent` /
  `Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent`;
- `lem-weil-pbc-limit-residue-field` /
  `WeilConjectures.AlgebraicGeometry.LimitResidueField`;
- `lem-trf-fp-module-limit-isomorphism-descent` /
  `Sheaf.AlgebraicGeometry.FinitePresentationLimitIsomorphismDescent`.

The existing general Picard theorem supplies arbitrary-base section lifting,
so another copy of that approximation argument is unnecessary. Some listed
modules can remain needed indirectly or by other consumers; they are not
withdrawn. The old projective-space properness dependency is replaced directly
by `lem-trf-projective-bundle-proper`. Quotient geometry, polynomial flatness,
and projective-space twist cohomology remain needed below the new geometry
lemma, rather than being pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan was a valid route, but it duplicated the arbitrary-base
lifting work already exposed by the Picard H1 generator theorem. Its empty
comparison family is sufficient because the projective-space fibre has
H1(O)=0. The existing general proper fibre-generator pullback-locus conclusion
exposes an unspecified finite locally free base module; a local proved helper
retains the unit itself, which makes tensor cancellation direct. No false
statement or tool defect was found, and no unit-level route is bypassed.

## New nodes

`lem-sfb-projective-bundle-fiber-geometry` in
`dag/nodes/sec-six-functors-basics/lem-sfb-projective-bundle-fiber-geometry.json`:
the pure geometry needed to apply the existing Picard H1 theorem to the
canonical projective bundle. Local frames identify the projection with standard
projective space; polynomial charts give flatness and finite presentation,
field-extension charts give geometric reducedness and connectedness, and the
degree-zero projective-space cohomology calculation gives H1(O)=0. The proof
and source references are recorded in both its docstring and its node. Three
Mathlib search types found no ready-made canonical-bundle theorem. There are
no change records because no existing interface or other module was changed.

Blueprint duplicate searches for "projective bundle" and "projective space"
found no existing blueprint statement of the combined canonical-bundle geometry.
The new node inherits the assigned node's explicit blueprint ancestor
`det-thm-sf-ctf-stability-direct-images`, with the existing via chain; it identifies
the geometry within the fibre-generator lifting part of that route. The ancestor
helper itself cannot follow the created.item chain because older split nodes
record a module there rather than a node id; the explicit inherited reference
preserves the recorded route.

Validation: ProjectiveBundleFiberGeometry compiled in 5.4 seconds and the complete
ProjectiveBundleFiberHomLift compiled in 21.1 seconds, without diagnostics in the
final runs. A source comparison confirms the assigned declaration's signature
and public imports are byte-for-byte unchanged. The delivered Lean files contain
zero and one sorry tokens respectively, all in the one named public geometry
theorem described above.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
