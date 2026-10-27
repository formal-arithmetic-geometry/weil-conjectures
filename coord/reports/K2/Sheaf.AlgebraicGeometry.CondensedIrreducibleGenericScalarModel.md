## What changed

Decomposed `AlgebraicGeometry.ProEtale.condensed_irreducible_generic_scalar_model`
into four strictly simpler inputs and a written descent proof. The proof preserves
the supplied generic isomorphism alpha, descends its restriction through a fully
faithful normalized component corner, pulls that very delta along every section,
and constructs the resulting model with the original scalar complex P.

The ordinary corner scalar comparison is proved by lifting the monoidal beta
comparison to modules and cancelling its coefficient isomorphism. The ordinary
scheme comparison uses the proved point-module linearity theorem and the
existing extension-to-restriction isomorphism, with its underlying map explicit. The
splitting is proved directly: faithful flatness gives going-down, fibre-product
points make the component map surjective, and extremal disconnectedness gives
its continuous section. The section equation and generic_induced are proved by
cancellation of specified isomorphisms.

The existing data block moves verbatim to CondensedGenericScalarModelData and is
publicly re-exported by the parent, allowing the separate step modules to refer
to it without an import cycle. See
`coord/changes/K2-generic-scalar-data-extraction.md`.

## Proved and sorry left

Closed the body of
`AlgebraicGeometry.ProEtale.condensed_irreducible_generic_scalar_model` by
composition from four named proof steps. This is a decomposition, not a net proof:
one original hole closed, four holes added, net minus three. The parent has zero
remaining holes. New holes, each exactly `:= by sorry` in its own module:

- `AlgebraicGeometry.ProEtale.CondensedGenericScalarModel.geometric_field_perfect_model`
  (lem-zl-condensed-geometric-field-perfect-model).
- `AlgebraicGeometry.ProEtale.CondensedGenericScalarModel.contractible_corner_lisse_lift`
  (lem-zl-condensed-contractible-corner-lisse-lift).
- `AlgebraicGeometry.ProEtale.CondensedGenericScalarModel.generic_fiber_corner_fully_faithful`
  (lem-zl-condensed-generic-fiber-corner-fully-faithful).
- `AlgebraicGeometry.ProEtale.CondensedGenericScalarModel.slice_section_comparison`
  (lem-zl-condensed-slice-section-comparison).

The data module has no holes. Source-parser checks confirm that all 14 existing
declaration signatures and every moved data body are unchanged. The extracted
data namespace is also byte-for-byte identical to its original source. The DAG
closure has no cycles. The new lemmas are respectively about a geometric
point, the U corner alone, the fibre corner alone, and arbitrary profinite sections;
none restates the combined generic model theorem or packages its hypothesis.

## No longer needed

Removed the direct proof imports of
`Sheaf.Paper.GeometricFieldProEtaleEvaluation`,
`Sheaf.AlgebraicGeometry.GenericFiberComponentsSection`, and
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` from the parent. Their
mathematical inputs are still needed inside the new compatibility steps; no
claim is made that these modules leave the target closure. Removed their two
direct tool_uses approvals from the parent's node because its actual proof now
uses the named compatibility steps. No module or mathematical node is withdrawn.
The public imports formerly supporting the data stay in the extracted data
module and remain publicly available through the parent.

## Where the brief, the DAG or earlier work was wrong

The old four-step plan is mathematically correct, but its formal interfaces do
not directly line up. GenericFiberComponentsSection uses sectionwise modules
and a differently normalized component functor; the current CoverModel requires
the fixed internal-module corner with specified adjunction-mate equations.
Likewise the w-contractible evaluation equivalence uses its own coefficient
comparison. The new lift and full-faithfulness steps make those normalization
comparisons explicit. The profinite section needs a Slice along an arbitrary
continuous map, whereas ComponentDerivedSquare.System supplies slices only along
maps induced by affine schemes. The separate section-comparison step supplies
exactly this missing interface. No statement was weakened and no unit route was
changed. Checked edge cases include empty U/fibre, zero coefficient ring, zero
complex, and the case X is a point; no coefficient flatness is introduced.

## New nodes

`def-zl-condensed-generic-scalar-model-data` owns the existing extracted data;
all declaration names, types, and bodies remain unchanged.

`lem-zl-condensed-geometric-field-perfect-model` is HRS Lemma 4.1(2) at a geometric
point, with the scalar section-ring comparison made explicit.

`lem-zl-condensed-contractible-corner-lisse-lift` is HRS Proposition 4.3(3),
transported to a given normalized component corner.

`lem-zl-condensed-generic-fiber-corner-fully-faithful` is the equivalence on the
right of HRS (4.4), transported to the normalized corner. It requires neither
irreducibility nor genericity and states no scalar model conclusion.

`lem-zl-condensed-slice-section-comparison` is the inverse-image identity and
scalar compatibility along a profinite section, including their mate formulas.

Every new theorem includes its source and a full proof in words. Searches used
LeanFinder, LeanSearch, Loogle and local library/Mathlib grep. The existing unit
and chapter route remain unchanged.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
