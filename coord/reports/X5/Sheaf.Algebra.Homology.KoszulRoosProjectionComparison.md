## What changed

The original `CategoryTheory.KoszulRoos.koszulRoosProjectionComparison` has a complete
combination proof from normalized chain models and coefficient coherence. Its signature is
unchanged. The proof establishes the explicit comparison's invertibility, projection square,
naturality, the actual constant-tower diagonal inverse, the derived projection-adjoint
identity using K-flat replacement, the iterated Koszul cone transition, and the interval bound.

The unchanged definitions were extracted into `KoszulRoosComparisonData` and publicly
reexported by the original module, so the two supporting lemmas can import them without a
cycle. Every moved declaration's text was checked against the repository original and is
identical. The packet selects the existing Koszul source's local tensor instances; the
monoidality witnesses are proposition proofs and the resulting tensors are definitionally
equal. No adopted source-library file or target is edited.

Change record: `coord/changes/X5-koszul-roos-comparison-data.md`.
The original definitions were compared as one exact text block; the original theorem's
signature was compared separately and is also identical. The consumer query reports zero
existing downstream Lean modules. The shared definitions compile in 38.2 seconds and the
main proof compiles cleanly in 24.3 seconds on the prescribed compile server.

## Proved and sorry left

Original hole removed: `CategoryTheory.KoszulRoos.koszulRoosProjectionComparison`
(`lem-sp-koszul-roos-projection-comparison`). The original module has no remaining `sorry`.
This is a decomposition, not an axiom-closed proof of the target closure.

Two holes are added, each in its own public theorem and module:

- `CategoryTheory.KoszulRoos.normalizedKoszulRoosModels`
  (`lem-sp-normalized-koszul-roos-models`): existence and normalization of the chain models,
  the source argument's steps 1--6 and 11. It omits every `Compatibility` conclusion proved
  in the original module, including the projection-adjoint identity and interval bound.

- `CategoryTheory.KoszulRoos.koszulRoosCoefficientCompatibility`
  (`lem-sp-koszul-roos-coefficient-compatibility`): coherence of quotient changes for
  already normalized models. It asserts no model existence or regularity and is the
  separate source step 12.

The retained construction and coefficient lemmas are genuine parts of the source proof;
each omits the projection-adjoint and constant-tower calculations completed in the main
module. Each has its full statement, source, complete proof in words, and its own node.
There is no `sorry` in a definition, private helper, or intermediate part of the combination
proof. Holes closed: 1; holes added: 2; net closure change: -1. This is a decomposition.
The retained model-existence statement compiles in 2.8 seconds.

A longer coefficient proof was developed and repeatedly compiled in this session. Its
signed Roos and derived-transition portions reached compilation, but the complete proof
was not verified. It is not included in the delivery or counted as proved.

## No longer needed

No module is withdrawn and no globally unreachable module is claimed.

The original module's former private imports of
`Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`,
`Sheaf.Algebra.Homology.KInjectiveProductsTermwise`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.CategoryTheory.StrictRoosComparison`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Sheaf.Paper.RingedScalarExtensionComplexAdjunction`, and
`Sheaf.Paper.RingedTopoiTensorSections` are not needed by its combination proof.
The original public imports remain available through `KoszulRoosComparisonData`.
The K-flat-resolution import stays because the arbitrary-complex adjoint calculation uses it.

The route no longer needs `lem-weil-strict-roos-comparison`: deriving the strict Roos
functor itself with `lem-weil-strict-roos-derivation` supplies its normalized unit. The
conservativity step uses the exact-functor homology comparison, so it needs no
`lem-weil-pbc-hom-into-triangle-exact`. The finite-tail existence part retains its own
finite-prefix argument and its stated dependencies. The separate K-injective resolution and
K-injective-product inputs are replaced in the normalized-model proof plan by the proved
`lem-weil-derived-countable-products-core` universal property; no global pruning is claimed. The original node's proof and
proof-dependency lists now describe the actual combination proof and the supporting nodes carry their own inputs.

The original node's obsolete top-level approvals are removed for
`lem-cbc-regular-quotient-cone-augmentation`, `lem-pc-derived-adjoint-functors`,
`lem-pc-ringed-space-product-kinjective`, `lem-pur-derived-change-of-rings`,
`lem-sf-exact-functor-derived-triangulated`,
`lem-weil-pbc-complex-ses-homology-long-exact`, `lem-weil-pbc-hom-into-triangle-exact`,
`lem-weil-proetale-countable-products-exact`, `lem-weil-strict-roos-comparison`, and
`prop-pur-kinjective-resolutions-exist`. The inputs still needed for model existence are
recorded on that new construction node; the preceding paragraphs explain the replacements.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical change is asserted. New supporting statements were
checked at m=k, the first power, the empty prefix, a unit section, and the zero ring. The original definitions were all
located in the theorem module, which prevented an independent supporting module from
referring to them without an import cycle. The extraction fixes that module boundary while
preserving the definitions and statement. Implicit matching of the two existing tensor
instance wrappers also caused large localization unfoldings; the packet uses the source's
local instance choices consistently.

The independent-reader and consumer checks are for the maintainer. There is no second
reader section for a dispatcher worker, as instructed by the brief.

## New nodes

`def-sp-koszul-roos-comparison-data` attaches the existing, verbatim comparison definitions
to their new shared module. It adds no mathematical construction and has no hole.

`lem-sp-normalized-koszul-roos-models` states only normalized chain-model existence,
including the signed tensor/Roos interchange and finite-prefix deletion. This is the
construction portion of the original proof and is independent of its projection-adjoint
calculation.

`lem-sp-koszul-roos-coefficient-compatibility` states coherence of coefficient changes for
any normalized models. Its proof is the distinct ordinary-unit, localized-scalar, and
signed-Roos naturality argument in source step 12.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
