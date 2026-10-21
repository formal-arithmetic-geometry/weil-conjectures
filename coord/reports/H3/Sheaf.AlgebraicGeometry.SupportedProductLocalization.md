## What changed

Reduced the two component-extension holes in SupportedProductLocalization to one
separate connecting-map theorem. Both maps now construct TriangleMorphism with
exactly the three existing components. The support-inclusion and open-restriction
squares in both variables have complete Lean proofs. All existing distinguishedness,
coefficient naturality, open naturality and open-row proofs are preserved, as are
every existing signature and public definition body.

SupportedTensorComparisonNaturality proves that the ordinary coefficient tensor
square descends to the normalized derived square. SupportedExteriorProductSupportMaps
uses it to prove support-map naturality of the actual supportedExteriorProduct:
conjugate the kernel inclusions, cancel the epic constant quotient, derive the
coefficient square, identify the projected evaluation counits and transpose.
The calculation keeps the native scheme tensor explicit; converting that tensor
back to generic tensor notation expanded the derived monoidal construction.

The target module's new private helpers identify successive support transports and
the product-open comparison. This identifies the target restriction with the
restriction appearing in the existing openFirst/openSecond formulas. Canceling the
third comparison gives both restriction squares. Support-map naturality, together
with the product-intersection equality, gives both inclusion squares.

The remaining boundary calculation is stated independently in
SupportedExteriorProductBoundary, with both tensor shift signs and a full sourced
coefficient-cone proof in words. It is strictly the third square, not another
assertion of either triangle morphism. It does not assume either of the first two
squares. The main proofs combine the four proved squares and the two boundary
equations into actual triangle morphisms.

## Proved and sorry left

Original holes closed in the item:

- AlgebraicGeometry.Etale.supportedProductLocalizationFirst_map.
- AlgebraicGeometry.Etale.supportedProductLocalizationSecond_map.

New hole:

- AlgebraicGeometry.Etale.supportedExteriorProduct_boundary, in
  Sheaf.AlgebraicGeometry.SupportedExteriorProductBoundary; node
  lem-pur-supported-exterior-product-boundary. Its single assertion contains the
  connecting-map equations in the two variables.

This is a decomposition from two holes to one, not an unconditional proof of the
localization theorem. The item itself has zero sorry occurrences. No sorry occurs
inside a definition or a private lemma.

The two additional public results are proved without new holes:
AlgebraicGeometry.Etale.supportedDerivedComparison_naturality and
AlgebraicGeometry.Etale.supportedExteriorProduct_supportMaps. Their supporting
ordinary, cochain, derived adjunction and generic composition calculations are proved.

## No longer needed

No existing Lean module or declaration is withdrawn, and no existing import is
removed. In particular, source-library declarations are preserved.

The planned direct dependency lem-pc-derived-tensor-second-factor-functor is not
used: the existing native tensorRight/tensorLeft exact functors and their CommShift
instances already give the required source triangles. Its obsolete top-level
tool_uses entry is removed from the item's node. This does not claim the helper's
module is unused elsewhere in the library.

The coefficient-Hom, stalk-flatness, K-flat and cone-pairing steps formerly listed
directly in the item's proof now belong to the boundary node, where they are still
needed. They are not claimed pruned. The proof dependencies of the two map nodes
now name the actual support-map, open tensor and connecting-map inputs.

The exploratory coefficient-localization and restriction probe files are omitted;
only the four intended Lean modules are delivered.

## Where the brief, the DAG or earlier work was wrong

The map nodes each cited their parent localization theorem in both statement and
proof dependencies, while the parent proof cited the map nodes. Their statements
now spell out the unchanged context and cite the definition nodes, and their proofs
cite the three actual squares. This removes those two local dependency cycles.
The existing Lean signatures are unchanged. Pre-existing cycles farther below this
item are outside this delivery.

The external derived-Hom cone theorem supplies a cone pairing, but its global-Hom
objects are not definitionally the normalized supported-section functors. A use of
that theorem still needs the supported-Hom coefficient, evaluation and boundary
comparisons described in the plan. The separate boundary node records precisely
that remaining argument; merely applying the cone theorem would not close it.

Further work on the boundary established in a scratch compilation the ordinary
A-linear equivalence Hom(C_b(A),F) ≃ Γ_b(F) and its naturality in F. Its map sends f
to the value at 1 of its adjoint. The boundary docstring now records this concrete
normalization and the fromSingleEquiv route to cochain models. Matching the resulting
derived comparison, coefficient sequence and normalized connecting maps remains.
The unused scratch probe is omitted from the delivery.

## New nodes

lem-pur-supported-tensor-comparison-naturality: proved descent of ordinary coefficient
tensor naturality through signed total complexes and the mixed tensor universal
property. Its new module has one public theorem and no holes.

lem-pur-supported-exterior-product-support-maps: proved naturality of the supported
exterior product under normalized inclusions of supports. It applies without
boundedness, finite type or finite coefficient assumptions. Its new module has one
public theorem and no holes.

lem-pur-supported-exterior-product-boundary: the genuinely separate connecting-map
calculation in both variables, with the actual normalized boundaries, geometric
comparisons and signed tensor shift maps. Its one public theorem is the one new
sorry, with source, complete proof in words and empty/full-support edge checks.

Change record: coord/changes/H3-supported-localization-component-proofs.md.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
