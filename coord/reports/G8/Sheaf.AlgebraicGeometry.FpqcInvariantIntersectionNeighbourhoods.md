## What changed

Proved `CategoryTheory.Over.DescentDatum.exists_fpqc_invariant_intersection_neighbourhood`
in `Sheaf.AlgebraicGeometry.FpqcInvariantIntersectionNeighbourhoods`, preserving its full
signature and the definition of `descentRelationTarget`.

The proof constructs inversion of the descent relation, proves it is an involution,
and uses it to transfer flatness and affineness from the pullback projection to the
target. Naturality and the identity law give a common section. Singleton-orbit
saturation extends to arbitrary subsets by unions. Applying the existing compact-image
lemma to an affine neighbourhood gives K and H; the existing complement lemma gives W.
Applying the compact-image lemma to H gives E and its nonempty intersection family.
The final extensionality argument converts ambient open subsets into scheme opens.

Added proof imports of `WeilConjectures.AlgebraicGeometry.TransportLeftNaturality`,
`Sheaf.AlgebraicGeometry.FlatRelationQcImageIntersections`, and
`Sheaf.AlgebraicGeometry.FlatRelationInvariantOpenComplement`. Updated the existing
node's proof to record inversion, naturality and the final family conversion.
No public imports, definitions, theorem signatures or consumer modules changed.

Validation: lcompile.py compiled the complete proof in 4.0 seconds. Its only warning
was a deprecated set-membership simp lemma, now replaced by `Set.mem_ofPred_eq`;
the delivery compile and axiom probe check the final file again. Both new proof
imports pass import_direction.py. The empty ambient scheme case is vacuous over v;
the common-section and saturation arguments apply to empty subsets as well.

## Proved and sorry left

Closed 1 existing hole:
`CategoryTheory.Over.DescentDatum.exists_fpqc_invariant_intersection_neighbourhood`
(node `lem-a1-fpqc-invariant-intersection-neighbourhoods`).

Zero holes remain in the item; zero holes added; zero statements split off.
This is a proof from existing stated dependencies, not a claim that all transitive
dependencies are sorry-free. In particular the existing declarations
`AlgebraicGeometry.flat_relation_qc_image_intersections`
(`lem-a1-flat-relation-qc-image-intersections`) and
`AlgebraicGeometry.flat_relation_invariant_open_complement`
(`lem-a1-flat-relation-invariant-open-complement`) still contain their original holes.

## No longer needed

Removed direct proof imports:
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.Properties`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `WeilConjectures.Topology.SpectralGeneralizations`

The current DAG's two existing topology lemmas already encapsulate the long arguments
of the older module docstring. Consequently this module needs no direct application
of `lem-weil-pbc-spectral-generalizations-of-quasi-compact`; its obsolete direct
tool-use entry is removed. That spectral result remains needed inside the image
lemma, and no global withdrawal or pruning of that dependency is claimed.
All current mathematical proof dependencies are retained; the naturality node is
added to record the precise existing lemma used by the relation calculations.
No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The module docstring retains the original eight-step proof, whereas the current DAG
already factors its topology into two stated lemmas. This delivery implements the
current DAG assembly. No false statement, definition defect or tool failure found.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
