## What changed

Kept the statement of
`AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_comparison_coherence`
unchanged. The proof checks ordinary composition and identity using the recorded
extension/restriction adjunction: maps out of scalar extension are determined by
`1 tensor x`. The sections formulas and the normalization formulas give the two
ordinary diagrams and the explicit composite-sections equation.

The derived paths are packaged as natural transformations. Equality on flat-term
K-flat models extends to all derived objects by `Localization.natTrans_ext`, a
K-flat resolution, naturality and cancellation of the image of its
quasi-isomorphism. Flatness and K-flatness of component restrictions use the
existing clopen detection declaration. This uses the existing resolution theorem
directly instead of the larger derived tensor descent interface.

Two new modules separate the fixed-model composition and identity calculations.
They assume the corresponding ordinary diagram (proved in the item), the
normalized representative laws and the model hypotheses. They omit both the
ordinary tensor argument and extension from models. Their docstrings give the
counit cancellation arguments, including equality transports. No definition,
existing public signature or public import was changed. The item adds private
proof imports for the two model modules, K-flat resolutions and the explicit
sheaf-tensor comparison used to express flatness of the resolution terms.

## Proved and sorry left

The original item had one hole, in
`AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_comparison_coherence`.
Its body now contains no `sorry`: it combines the ordinary calculations with the
two model assertions using a proved resolution/naturality argument.

Two holes are added, each the entire proof of one named public theorem:

- `AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_composition_model`,
  node `lem-pur-clopen-scalar-composition-model`;
- `AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_identity_model`,
  node `lem-pur-clopen-scalar-identity-model`.

This is a decomposition: one upper hole closed and two strictly smaller model
holes added, net minus one. It is not a complete proof from already proved
lemmas. The item has zero holes left; the delivery has two. All private helpers
are proved, including `model_ext`, `tensor_ext`, `tensor_map_one`,
`tensor_transport`, `restricted_tensor_ext`, `ordinary_comp` and `ordinary_id`.
All three modules compile through `lcompile.py`; the item compiled in 38.4 seconds.
Two redundant `change` tactics reported by the linter were then removed; the
delivery command performs the final compile and all required packet checks.

## No longer needed

No original Lean import was removed. The original module publicly imported only
the scalar data module, which remains necessary for its statement.

The proof no longer needs the full
`lem-weil-pbc-site-derived-tensor-descent` /
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
as a direct proof dependency: a resolution and naturality suffice for equality
of natural transformations. Its module was never imported by the item.

The original direct proof dependency
`lem-sfb-successive-derived-quotient-normalization` is also unnecessary as an
existence theorem: the item already takes normalized families as parameters and
uses their fields. Its data and normalization APIs remain available through the
required scalar data module. The tensor definition
`def-pur-sheaf-tensor-product` remains a dependency of the scalar data and tensor
comparison; it is not withdrawn. These observations are local to this proof;
none of those shared declarations or modules is deleted or claimed globally
unused.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is sound. The source's representative computations require
flatness and K-flatness after restriction as well as before restriction; the
parent proof now obtains these explicitly from the existing clopen detection
statement. The localization-density step can use the existing K-flat resolution
theorem directly and does not require the larger derived tensor descent theorem.

`tools/blueprint_refs.py ancestor` returned no ancestor for the item because its
`created.item` records a Lean module name rather than the parent node id. The
new nodes record the actual blueprint ancestor `def-pur-section-invariant`, as
seen in the parent compositor's blueprint record. The whole-blueprint search
`scalar clopen` found only `def-pur-supported-cup`, which is not either of the
fixed-model calculations. Empty components, zero rings and zero complexes do not
invalidate any cancellation or generator argument; all canceled maps are recorded
isomorphisms.

## New nodes

`lem-pur-clopen-scalar-composition-model`, module
`Sheaf.AlgebraicGeometry.ProEtaleClopenScalarCompositionModel`, isolates the
composition counit calculation for a fixed flat-term K-flat model with a suitable
restriction, assuming the ordinary composition diagram. It has no units and no
finite-cover or arbitrary-derived-object conclusion.

`lem-pur-clopen-scalar-identity-model`, module
`Sheaf.AlgebraicGeometry.ProEtaleClopenScalarIdentityModel`, isolates the identity
counit calculation on such a fixed model, assuming the ordinary multiplication
diagram. It has no compositor or composition conclusion. The original node's
proof and proof dependencies now follow the ordinary calculations, resolution
argument and these model calculations. The unit route is unchanged. No change
record is required because this delivery changes no existing statement or
definition.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
