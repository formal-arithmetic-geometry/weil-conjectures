## What changed

Replaced the hole in `SupportedTrace.insertion_projection` by an assembly of both
coordinate identities, preserving its signature and all existing public imports.
The proof imports two new modules privately: `SfProperSectionProjection` and
`SfDiagonalPushComparison`. No other existing Lean module is changed.

The private proofs establish inverse ordered-projection naturality, factor the
insertion into its unit part and tensor with the arbitrary class, and prove the
restriction of the common-base coordinate comparison along the diagonal. The latter
is a complete calculation with the two source-library pullback associativity
identities, followed by naturality along `coefficientPull`. Two general categorical
assembly lemmas cancel the forward and inverse projection maps. Neither the arbitrary
diagonal class nor a triangular identity is assumed in a new theorem.

The complete assembly is proved in a private theorem with fixed proof-local instances.
The public declaration keeps its original instance scope and applies that proved
assembly. Its statement refers to no private helper.

The insertion calculation first uses naturality at the natural-transformation level
and then takes components. The section normalizations use equality of the whole
canonical isomorphisms before taking components. This avoids expensive kernel
conversion through their compactification constructions. Local reducibility and
instance settings follow the source's component-calculation conventions; no shared
definition, instance, attribute or public interface is changed.

The new definitions `properSectionPushIso` and `properSectionTensorIso` explicitly
construct the direct-image and tensor-unit comparisons for an arbitrary proper
section. They generalize the coordinate-specific `diagonalFirst`, `idIsoDiagonalSnd`
and `diagonalIso`. Their bodies compose the existing canonical isomorphisms and do
not choose data from an unproved theorem. Searches of the source and Sheaf trees for section,
projection, and `rightDerivedLowerShriekCompIso` found no existing generic definition
of this comparison. The relevant STATE module-sheaf encoding and canonical-map rules
are followed: everything remains on the original étale `DerivedCategoryModule`,
using the source's chosen functors and maps.

Validation: `lcompile.py` accepts both new modules (34.7 s and 42.0 s) and the
finished item without diagnostics (13.2 s). Both proof imports pass the import-cycle
check. The original public theorem signature and public imports were compared
verbatim, and all delivered Lean lines are at most 100 characters.

## Proved and sorry left

One original hole is discharged: `AlgebraicGeometry.Etale.SupportedTrace.insertion_projection`
(node `lem-sf-diagonal-insertion-projection`). It is a decomposition, not a net hole
reduction: two new named holes remain, each in a separate new module:

- `AlgebraicGeometry.Etale.SupportedTrace.properSectionProjectionUnit`
  (`lem-sf-proper-section-projection-unit`). This is the tensor-unit projection law
  for an arbitrary proper section; it has no diagonal class, common-base coefficient,
  trace or coordinate interchange.
- `AlgebraicGeometry.Etale.SupportedTrace.diagonalPushComparison`
  (`lem-sf-diagonal-push-comparison`). This is a direct-image compositor identity on
  diagonal-supported objects, involving no tensor product or projection map.

All private lemmas are proved. Both new section comparison definitions have zero holes.
There are no holes left inside the original theorem or its module.

The two new statements were checked on the identity section, on the zero object,
and for the zero coefficient ring: the section formula reduces to the ordinary
unitor/projection normalization, and the direct-image formula to identity/composition
coherence. Both are independent of a trace or an integral normalization. Unlike the
original conjunction, neither asserts naturality in a diagonal class; that argument
is completed in the item.

## No longer needed

No original public import is removed and no existing module is withdrawn. Pruned
modules: none. The original abstract projection-composition theorem is not imported
into the item itself: its proper-section specialization is retained as a dependency
of the new section lemma. The symmetry, tensor-unit and canonical-comparison nodes
remain needed. The DAG now records the two concrete coherence obligations and the
completed naturality and pullback calculations, rather than leaving those
specializations implicit.

## Where the brief, the DAG or earlier work was wrong

The original mathematical argument is sound, but its named ringed-topos coherence
statements use a different presentation from these concrete étale compact-support
functors. A direct application does not identify the source's chosen projection,
section and direct-image isomorphisms. The new statements isolate those two concrete
normalizations. The available `unboundedEtaleLowerShriekCompIso_assoc` and unit laws
in `UnboundedEtaleCompactSupportComparisons` require Noetherian schemes; the item
has no such hypothesis, so they cannot be applied directly or used to add that
hypothesis here. No statement or shared definition is weakened or changed.

## New nodes

`lem-sf-proper-section-projection-unit`, in `SfProperSectionProjection`, is precisely
the projection-composition section specialization at the tensor unit. Its docstring
and node give the source and the full argument, including normalization through the
proper forget-supports comparisons.

`lem-sf-diagonal-push-comparison`, in `SfDiagonalPushComparison`, is precisely the
associativity/identity comparison needed to interchange the two coordinates on
objects already supported on the diagonal. Its proof plan does not use either
projection or the diagonal class.

Both nodes lie in the item's original chapter and unit. The unit's route is
unchanged. No change record is required because no existing interface is changed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
