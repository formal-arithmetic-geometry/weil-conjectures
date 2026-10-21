## What changed

Completed the Lean proofs of
`AlgebraicGeometry.Etale.supportedProductLocalization_openFirst` and
`AlgebraicGeometry.Etale.supportedProductLocalization_openSecond` from the two
coefficient tensor restriction squares below. The proofs transpose through the
actual supported coefficient adjunction, prove the cut and uncut evaluation
identities, apply tensor naturality, and transport all projection and pullback
comparisons explicitly. The original statements and all existing public imports
are preserved. The item adds one private proof import,
`Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor`.

Added ten modules. Eight contain complete proofs: the ordinary support mate's
quotient normalization, the unbounded exact-derived mate calculation, the
complex-model normalization of the derived support mate, ordinary tensor-square
normalization by epic constant quotients, both canonical ordinary open-product
tensor squares, the generic passage from ordinary squares to signed total complexes, and its
application to the actual first-open coefficient square. The ordinary factor maps are also constructed as natural
transformations, with their component formulas proved, for direct use by exact
derivation. The remaining two state the coefficient tensor squares needed by the two completed proofs. Their maps
are constructed explicitly from the actual support restriction and canonical
projection comparisons. All definitions contain real constructions. The complex-square condition is
packaged as an irreducible proposition with a proved generic API, avoiding
repeated expansion of tensor-complex structures at scheme functors; no compilation
limit is raised. The specialized complex square now compiles in 10.4 seconds
(the original direct expansion exceeded 60 seconds).

Updated step 11 and the proof dependencies of
`lem-pur-supported-product-localization`; the other localization-map proof steps
are retained. No existing statement, definition, target, or source-library file
was changed. No consumer adaptation is required. The added file-scoped proof
elaboration option is recorded in
`coord/changes/B6-supported-product-localization-elaboration.md`.

Validation: all eleven sandbox Lean modules compile in import order, without errors
or warnings. The ordinary open tensor calculations, the generic signed-complex
calculation, and its first-open specialization are complete proofs. New statements include arbitrary unbounded
coefficient complexes; their arguments include empty opens, empty supports,
zero coefficients, and non-flat coefficient modules.

## Proved and sorry left

Four holes existed in the item. Two upper holes are closed:

- `AlgebraicGeometry.Etale.supportedProductLocalization_openFirst`.
- `AlgebraicGeometry.Etale.supportedProductLocalization_openSecond`.

Two original holes remain unchanged:

- `AlgebraicGeometry.Etale.supportedProductLocalizationFirst_map`
  (`lem-pur-supported-product-localization-first-map`).
- `AlgebraicGeometry.Etale.supportedProductLocalizationSecond_map`
  (`lem-pur-supported-product-localization-second-map`).

Two strictly coefficient-level holes are added, one per new module:

- `AlgebraicGeometry.Etale.supportedCoefficientTensor_openFirst`
  (`lem-pur-supported-coefficient-open-tensor`).
- `AlgebraicGeometry.Etale.supportedCoefficientTensor_openSecond`
  (`lem-pur-supported-coefficient-second-open-tensor`).

Thus the two open identities are a decomposition, not a net reduction of the
hole count: two holes closed, two added, net zero. The retained coefficient
statements still require derived tensor descent and identification with the
specified derived projection comparisons. Their ordinary coefficient squares,
the common signed-totalization calculation and the ordinary-to-derived mate
normalization are proved in this packet. The statements contain no
supported-section inputs or evaluation maps. They isolate
the coefficient normalization/descent part of step 11; the adjunction and
section-evaluation argument combining them into the item is fully proved.

The remaining derived step has two specific comparison obligations. First,
identify `Functor.exactDerivedMap` of each ordinary factor natural transformation,
followed by `Functor.mapDerivedCategoryCompIso`, with the displayed derived factor
maps. This includes the projection-square and projection-composition coherence;
the product mate's complex normalization is already proved. Second, combine the
signed complex square with the model normalization of
`supportedCoefficientTensorDerived` and
`leftDerivedUpperStarTensorComparison_app_app_comp`, retaining the exact versus
left-derived pullback isomorphisms. The existing generic monoidal comparison
lemmas apply to monoidal functors; the supported coefficient pairings here have
three different coefficient functors, so they do not directly instantiate to
this square. The two retained source-backed statements isolate this common
derived-coefficient argument, with both ordinary squares and their natural
transformations supplied here.

The following additional results are proved with no new holes:

- `AlgebraicGeometry.Etale.supportedCoefficientOpenMate_quotient`.
- `CategoryTheory.Adjunction.derivedExact_mateEquiv_app_fac`.
- `AlgebraicGeometry.Etale.supportedCoefficientDerivedOpenMate_fac`.
- `AlgebraicGeometry.Etale.supportedCoefficientTensor_quotientSquare`.
- `AlgebraicGeometry.Etale.supportedCoefficientTensor_ordinaryOpenFirst`.
- `AlgebraicGeometry.Etale.supportedCoefficientTensor_ordinaryOpenSecond`.
- `AlgebraicGeometry.Etale.supportedTensorComplex_square`.
- `AlgebraicGeometry.Etale.supportedCoefficientTensor_complexOpenFirst`.

There are exactly four explicit `sorry` occurrences in the delivery's Lean
files, all in the named public theorems listed above. No private theorem or
definition contains a hole.

## No longer needed

No existing imports, nodes, or modules are withdrawn. The initially considered
proof import `Sheaf.AlgebraicGeometry.OrdinaryKunnethMap` is unnecessary and was
removed from the new quotient-square module; that module compiles directly from
`SupportedExteriorProduct`. This does not withdraw OrdinaryKunnethMap or any
existing node. The two open-identity
proofs need only the coefficient squares and elementary adjunction/tensor
naturality. The coefficient-Hom and cone dependencies remain needed by the two
unfinished localization-map arguments, so their edges and modules are retained.
The parent dependency update removes no old proof edge. No unit statement or
unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect definition was found. Step 11 expresses open
naturality in words without a separate Lean declaration for its coefficient
tensor square. The new coefficient lemmas make precisely that part explicit.
The unbounded support adjunction needs the unbounded mate calculation; the
existing bounded-below mate theorem alone does not instantiate for arbitrary
coefficient complexes. Its unbounded analogue is proved here from the existing
unit/counit factorization API.

## New nodes

`lem-pur-supported-coefficient-open-mate-quotient` attaches the ordinary quotient
normalization and the constructed generic mate. Its theorem is proved.

`lem-pur-exact-derived-mate` attaches the unbounded derived mate calculation and
the localization of transformations of exact functors. Its theorem is proved.
The two generic existing dependency nodes are declared as tool uses.

`lem-pur-supported-coefficient-derived-open-mate` attaches the constructed
derived support coefficient mate and its complex-model formula. Its theorem is
proved.

`lem-pur-supported-coefficient-open-tensor` attaches the first-variable
coefficient square and its canonical factor comparisons. Its theorem is the
first retained source-backed coefficient hole.

`lem-pur-supported-coefficient-second-open-tensor` attaches the second-variable
coefficient square and its canonical factor comparisons. Its theorem is the
second retained source-backed coefficient hole.

`lem-pur-supported-coefficient-tensor-quotient-square` attaches the proved
ordinary tensor-square normalization by three constant quotients.

`lem-pur-supported-coefficient-ordinary-open-tensor` and
`lem-pur-supported-coefficient-ordinary-second-open-tensor` attach the two proved
ordinary open-product tensor squares, with their actual projection comparisons.

`lem-pur-supported-tensor-complex-square` attaches the proved generic signed
totalization step. It is recorded as a dependency of both retained coefficient
squares; their ordinary steps now cite the two completed ordinary squares.

`lem-pur-supported-coefficient-complex-open-tensor` applies the totalization
theorem to the actual first-open support mate and coefficient natural
transformations. Its theorem is proved and is cited by the first retained
derived coefficient lemma.

All ten nodes are in `sec-smooth-purity`, retain the parent's unit, give full
proofs in words, record Mathlib searches, and point to the supported Kunneth
blueprint ancestor through the existing localization node. The file-scoped
elaboration option is documented in
`coord/changes/B6-supported-product-localization-elaboration.md`; downstream
inspection reports no importing modules and no consumer adaptation is needed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
