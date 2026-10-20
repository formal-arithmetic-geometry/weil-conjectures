## What changed

The original finite-level theorem now follows from the adopted arbitrary-finite-ring
`isIso_kunnethMap_of_isSepClosed`, once the canonical absolute/relative comparison is supplied.
The private coefficient proof constructs the required invertible exponent `l ^ n` from the
recorded DVR and proves finiteness using `Padic.finite_coefficientExtensionRing`. No coefficient
restriction, residue-field summand or nilpotent devissage is used in the new argument.

Moved the four generic map definitions unchanged into OrdinaryKunnethMap and publicly imported
that module from the item to avoid an import cycle with the comparison. AbsoluteKunnethComparison
constructs the right-adjoint comparisons by conjugacy and the transported relative map from
actual adjunction units, counits and tensor comparisons. No arbitrary isomorphism is chosen.
A scoped Ring-instance preference prevents expensive comparison of the two definitionally equal
quotient-ring presentations. All three delivery modules compile within the file limit with this preference.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Etale.isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing`
(node `lem-pur-ordinary-kunneth-finite-ring`). Its original signature is unchanged.

Private proved ingredients: `constantPresheaf_monoidal_eq`, `constantSheaf_monoidal_eq`,
`isIso_ordinaryGlobalKunnethMap_of_relative`, `isIso_ordinaryGlobalKunnethMap_finiteRing`, and
`finiteCoefficientRing_invertibleExponent` in the item's module.

The comparison module proves `transpose_comp_conjugate`,
`transpose_composite_adjunction`, `transpose_transport_tensorMate`,
`constantPullback_monoidal`, and `sectionsIso_counit`, together with the section and
pushforward monoidality lemmas they use. The derived tensor/composition coherence and
its final combination remain in the single public comparison obligation.

One added hole: `AlgebraicGeometry.Etale.ordinaryGlobalKunnethMap_eq_relative`, node
`lem-pur-absolute-kunneth-comparison`, in AbsoluteKunnethComparison. This is equality of two
explicitly constructed maps over arbitrary schemes and coefficient categories; it contains
none of the finite-field, finite-type or finite-coefficient hypotheses of the original theorem.
Its docstring and node give the full proof by adjunction transposition and constant-pullback
composition/tensor coherence. It is a separate categorical part of the argument, not the
original invertibility assertion under another name.

This is a decomposition: one original hole closed, one new hole added, net zero holes closed.
There are no sorries in definitions and no other holes in the delivered files.

The four moved definition bodies were compared verbatim with the original source. An auxiliary
formal equality check reconstructing them under the full original imports exceeded the file
limit; no successful formal equality check is claimed. The unmodified `SupportedProductLocalization` consumer compiles against the new public
re-export. The direct `ExternalRHomConePairing` check exceeded the file limit against both the new
module and the untouched original module (the original item itself compiled in 13.7 seconds).
This does not establish a forced adaptation, so the J7 consumer is unchanged. Temporary
consumer and baseline copies were removed from the packet.

The first delivery preflight found `CompactProductArrows` missing from the change record's
Users table. Re-ran the downstream name search, read its `compactProductMapCore` definition,
and added this unclaimed consumer to the record. Its unmodified module compiles against the
new re-export in 14.2 seconds; no consumer adaptation is needed. Removed its temporary copy
before resubmitting.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.ClosedImmersionProducts`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.Paper.FiniteFieldDerivedTensorSummand`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.KunnethGlobalSections`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The new argument no longer cites these old planned proof dependencies directly:

- `def-weil-finite-type-morphism`
- `lem-weil-pbc-closed-immersion-products`
- `lem-pc-separated-quasi-separated`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-pur-finite-field-derived-tensor-summand`
- `lem-kun-0f10`
- `lem-pur-derived-change-of-rings`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `def-kun-projection-formula-map`
- `lem-kun-0f12`
- `lem-kun-inverse-image-monoidal`
- `lem-pc-kflat-resolution`
- `lem-weil-pbc-site-derived-tensor-descent`
- `def-pc-kflat-complex`
- `lem-weil-pbc-complex-ses-triangle`

In particular the coefficient-restriction, finite-field tensor-summand, derived change-of-rings,
and finite nilpotent-filtration subarguments are unnecessary for this item: the adopted theorem
already allows an arbitrary finite coefficient ring with invertible exponent. No source-library
declaration or proved body was removed. Some old nodes remain transitive dependencies of the
adopted theorem (notably finite cohomological dimension and its projection-formula ingredients);
this report does not claim those nodes or their modules can be withdrawn globally.

Removed the old node's tool-use approvals only for dependencies no longer directly used; retained
existing approvals for `def-weil-l-adic-coefficient-extension`, `thm-kun-0f1p`, and
`def-kun-kunneth-map`. The unit's
statement and proof route are untouched (`sk-prop-a1-kummer.realized` is empty for this auxiliary).

## Where the brief, the DAG or earlier work was wrong

The planned residue-field reduction is unnecessary: the already proved upstream theorem takes
arbitrary finite commutative rings, not just prime fields. Its hypotheses are met by the actual
positive-level quotient using exponent `l ^ n`.

A nonempty isomorphism of the endpoints would not identify the specified absolute arrow. The
remaining comparison therefore states equality of the canonical maps and constructs every
transport isomorphism by adjunction conjugacy. The chosen constant-presheaf monoidal structure
must also be normalized to the standard identity-component structure; this normalization is
proved, not assumed. The quotient has two Ring instance presentations; the scoped preference
fixes elaboration without changing its data.

## New nodes

`def-pur-ordinary-kunneth-absolute-map`: attaches the four existing generic definitions to their
new module, OrdinaryKunnethMap. This is a relocation of actual construction data, with zero holes.

`lem-pur-absolute-kunneth-comparison`: equality of the canonical absolute arrow and relative
Kunneth transported through the constants/sections adjunctions. It isolates the categorical
comparison from coefficient arithmetic and the geometric Kunneth theorem.

Change record: `coord/changes/G7-ordinary-kunneth-definition-module.md`.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
