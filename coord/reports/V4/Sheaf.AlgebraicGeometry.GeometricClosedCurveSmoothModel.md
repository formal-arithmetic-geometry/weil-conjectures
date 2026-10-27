## What changed

Filled `WeilConjectures.FiniteFieldDatum.exists_smooth_closed_curve_finiteField_model`
without changing its signature or any definition. The proof applies the existing proved
finite-field closed-subscheme descent theorem, retains its embedding-compatible isomorphism,
and establishes affine finite type, fpqc descent of smoothness, geometric connectedness,
pure dimension one, and the universal closed-point/finite-residue-extension assertion.
The model is chosen before the point, including for an empty prescribed set.

Added private proved helpers transferring component and local dimensions along homeomorphisms.
The dimension step uses the existing scheme-level equidimensional-open and constant-local-
dimension component criteria, together with field-extension local dimension invariance.
Updated the existing node's proof, proof dependencies, and proof origin accordingly.

The two already proved criteria `lem-sbc-equidimensional-open-local-dimension` and
`lem-sbc-constant-local-dimension-components` are used as tools: they implement the two
component/local dimension transitions in the original argument. They do not bypass a step
of the assigned blueprint unit. No new mathematical statement or object is introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.FiniteFieldDatum.exists_smooth_closed_curve_finiteField_model`
(node `lem-zl-geometric-closed-curve-smooth-model`).

No `sorry` remains in the delivered module. Holes added: 0. Split off: 0.
The existing dependency `AlgebraicGeometry.field_extension_component_local_dimension`
remains a separately stated library theorem; its existing hole is not changed or duplicated.

## No longer needed

Removed the direct proof import `WeilConjectures.RingTheory.DimensionAtPointComponents`.
Also removed redundant private imports `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.AlgebraicGeometry.Pullbacks`, and `Mathlib.AlgebraicGeometry.PullbackCarrier`;
the needed interfaces and instances are already exported by the retained imports.
The proof uses existing scheme-level criteria instead of manually transporting the affine
prime-ideal component formula. The node `lem-weil-pbc-dimension-at-point-components`
is no longer a direct proof dependency, but remains a transitive dependency of existing
library results; its module and declarations are retained.

Removed the direct DAG dependency `lem-weil-pbc-fibre-product-affine-spectra`:
affineness, locally finite type, and quasi-compactness follow from existing base-change,
closed-immersion, and composition instances without constructing a tensor presentation.
No module is withdrawn and no globally unused module is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned affine component formula is stated only for spectra of finite-type algebras,
whereas the assigned theorem uses abstract schemes and a comparison isomorphism.
The existing proved scheme-level pure/local dimension criteria supply the required
transport directly. The last component assertion is obtained on the model's top open,
without introducing an identity-field-extension pullback.

The statement, finite-field model, and comparison isomorphism are unchanged. No definition
repair, consumer adaptation, or change record is required.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
