## What changed

Proved `CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`
in `Sheaf.CategoryTheory.InternalSectionTensorComparison`, preserving its complete signature.
The proof constructs the normalized tensor and unit comparisons, verifies naturality,
associativity, both unitors and symmetry on pure tensors, constructs the unbounded
sum-total comparison with its summand equation, and proves the acyclicity, flatness and
K-flatness equivalences. The counit of the termwise equivalence supplies all sectionwise
acyclic test complexes, without a boundedness restriction.

`Sheaf.CategoryTheory.InternalSectionModuleFlat` already contained a complete private
construction of the balanced tensor isomorphism. Added the proved public theorem
`CategoryTheory.InternalAbelianSheafModule.exists_sectionTensorIso`, exposing that
construction and its pure-tensor equation for the canonical presheaf tensor. The bridge
from the canonical presheaf tensor to `siteTensorPresheaf` is the identity on each section
tensor; naturality of the sheafification unit transports the equation. Existing declarations,
definitions, instances and public imports in this module are unchanged. Its existing
flatness theorem is reused. No module under `WeilConjectures` was edited.

Updated both existing DAG nodes to record this route and the added public API. The unit
`sk-def-pe-derived-completion` and its realized route are preserved. Change record:
`coord/changes/R5-section-tensor-comparison-api.md`. The consumer audit found two existing
consumer modules of the unchanged flatness theorem; neither needs adaptation.

Validation: `lcompile.py --all` compiled both delivered modules cleanly, in 21.0 seconds
and 56.4 seconds respectively. The target theorem and both public pure-tensor definitions
retain their original signatures verbatim.

## Proved and sorry left

Closed one hole:
`CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`
(node `lem-pe-internal-section-tensor-comparison`).

Added zero holes; split off zero holes. Zero sorries remain in either delivered Lean module.
The six infrastructure theorems in the item were already proved and are not counted as
holes closed by this delivery. The newly exposed `exists_sectionTensorIso` is fully proved.

## No longer needed

Removed these direct proof imports:

- `Sheaf.CategoryTheory.RingedSiteModules`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.CategoryTheory.SheafTensorStructure` (already a public dependency of `SheafTensor`).
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal` (already a public dependency of
  `ModuleObjects.Symmetric`).

Removed these direct proof dependencies from the item node:

- `lem-sfb-modobj-forget-left-exact` and `lem-sfb-modobj-forget-right-exact`: exactness follows
  directly from the equivalence; neither underlying forgetful exactness theorem is used.
- `def-weil-sheaf-of-modules-category`: the required category instances are already available;
  the `ringedSiteModules` wrapper is unused.
- `def-weil-pbc-sheafification`: the existing proved tensor comparison supplies the construction;
  its underlying abelian sheafification arguments need not be repeated in this item.
- `lem-pc-sheaf-modules-tensor-closed`: coherence uses the lax monoidal adjunction identities
  and the existing tensor structure, without the tensor-closed packaging theorem.

Added the two existing dependencies `lem-c2-internal-section-module-flatness` and
`lem-sfb-left-resolution-map-total-iso`. No modules are withdrawn: some removed direct
imports remain transitive dependencies or are used elsewhere. No upstream declaration is
removed or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction of the tensor universal property was unnecessary: the flatness
module already proves it privately. Exposing its normalized equation avoids duplicating
that argument. Exactness also follows directly from the equivalence, rather than from
separate exactness theorems for the two forgetful functors.

The canonical presheaf tensor and `siteTensorPresheaf` use different restriction-map
presentations, so their identification must be proved on tensor generators. They cannot
be interchanged merely by notation. The added API includes that identification.

The total-complex helper takes explicit hypotheses for the existing totalizations and for
preservation of their diagonal coproducts. This prevents repeated large typeclass searches;
the same totalization and the same unrestricted complex statement are used throughout.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
