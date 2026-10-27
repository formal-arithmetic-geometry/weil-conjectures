## What changed

The statement and the definition `quotientTensorPull` in
`Sheaf.Paper.QuotientPullbackTensorCoherence` are unchanged. The original theorem
is assembled from coefficient-map naturality, the existing section normalization,
and a tensor calculation restricted to flat-term K-flat complexes. A proved private
lemma `natTrans_ext_flat` extends an equality of two-variable natural transformations
from such complexes to all derived objects: choose two actual flat K-flat resolutions,
use the resulting product isomorphism, rewrite by naturality, and cancel its image.

The proved private helper `uncurryTensorComparison` constructs the natural
transformation on the product category explicitly: uncurrying a postcomposed
bifunctor requires the functor map-composition law.

The new module `Sheaf.Paper.QuotientPullbackTensorFlatModel` contains only the remaining
representative calculation. It keeps the actual normalized maps, and assumes neither
flatness of the quotient nor boundedness. Its proof in words explains the local balanced
generator calculation, the signed direct-sum total, localization, and transport back
from section modules. The original module's proof and node now describe the implemented
assembly. No shared definition or instance is changed.

Validation: both Lean modules compiled through `lcompile.py`; the final item compile
passed against the compiled new module. The original theorem signature and the
complete `quotientTensorPull` declaration were checked against the repository.

## Proved and sorry left

Closed in the item:
`AlgebraicGeometry.ProEtale.IntegralQuotient.quotient_pullback_tensor_coherence`
(originally one hole). The coefficient-square conjunct is proved directly by
`map_coefficientMap_comp_condensedPullbackHom`. The entire section-comparison
conjunct follows from `quotient_section_tensor_normalization`. The final conjunct
is proved by resolving both inputs and transporting the model equality by naturality.
There is no `sorry` left in the item module.

Added one hole:
`AlgebraicGeometry.ProEtale.IntegralQuotient.quotient_pullback_tensor_flat_model`,
node `lem-sfb-quotient-pullback-tensor-flat-model`. This is the tensor equation on
two given flat-term K-flat complexes, before the resolution and naturality extension.
It is a strictly restricted calculation from the old plan, with no coefficient-square
or section-data existence assertion. Its source and complete mathematical proof are
in its docstring and node. This delivery is a decomposition: one upper hole closed,
one lower hole added, zero net holes closed. It does not claim an axiom-free proof
of the representative calculation.

## No longer needed

Removed these private imports from the item:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`

The direct proof dependency `lem-pc-kflat-resolution` is replaced by the already
proved abstract resolution theorem `lem-sfb-abstract-kflat-resolution` in
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`. The direct proof dependency
`lem-weil-pbc-site-derived-tensor-descent` is replaced by the explicit private
naturality/cancellation proof. The direct proof dependency
`lem-sfb-ringed-derived-monoidal-comparisons` is unnecessary: the required normalized
section comparison is already supplied by `ComparisonSpec`. These three obsolete
top-level tool approvals are removed, preserving the order of the others.

The total-tensor, pullback-preservation, pullback-tensor, and section-calculus nodes
remain needed below the new representative calculation. Their removal from the main
module's direct imports does not assert that those modules can be globally withdrawn.
No module is deleted, and the proper-base-change unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic `Functor.map_leftDerivedTensorComparison_comp_eq_of_iso` theorem needs
exactness of scalar extension. The uniformizer quotient is generally nonflat, so
that shortcut cannot prove this statement. No exactness hypothesis has been added.
The old separate ringed-compositor reconstruction and site-level two-variable descent
are unnecessary for the assembly; section normalization and elementary naturality
already give those parts. No statement is disputed or weakened. No existing module
besides the assigned item, and no other existing node, is changed.

## New nodes

`lem-sfb-quotient-pullback-tensor-flat-model` records the tensor equation on given
flat-term K-flat complexes, in `Sheaf.Paper.QuotientPullbackTensorFlatModel`.
The ordinary generator calculation sends both routes to
`(p-tilde tensor 1) tensor (q-tilde tensor a s-prime)`. The maps preserve the ordered
bidegree, hence agree on the signed direct-sum total even for unbounded inputs.
The parent performs the separate resolution and naturality step in Lean.
Edge cases checked in the mathematical argument: zero inputs, the identity map,
the residue-field quotient (Lean index zero), and odd-degree homogeneous inputs.
No change record is needed because existing signatures and definitions are unchanged.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
