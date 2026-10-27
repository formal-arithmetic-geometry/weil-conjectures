## What changed

Construct the ordinary and derived section tensor comparisons by conjugating the supplied
internal comparisons through the fixed section equivalences. Cancel precomposition with an
equivalence using Mathlib `Equivalence.congrLeft` and its fully faithful inverse functor.
Private proof imports expose the existing normalized ordinary comparison and its monoidal
naturality theorem. The ordinary generator calculation uses the coequalizer projection and symmetry; naturality
extends it from the image of the section equivalence to all section modules. The derived
conjugation identity follows by cancelling the comparison isomorphisms. The remaining K-flat
computation equation is stated separately in `Sheaf.Paper.SectionTensorConjugateComputation`.
The original theorem's statement and all existing definitions are unchanged.
Four private proof steps submit existing equality proofs directly to the kernel after
simplifying their functor presentations. This avoids repeated elaborator conversion of
large chosen tensor structures; it does not bypass kernel checking.

## Proved and sorry left

The original hole `AlgebraicGeometry.ProEtale.QuotientChange.section_tensor_normalized_of_normalized`
is reduced to the smaller computation equation. One hole is added:
`AlgebraicGeometry.ProEtale.QuotientChange.section_tensor_conjugate_computation`, node
`lem-sfb-section-tensor-conjugate-computation`. This is a decomposition, not a net hole closure.
The new theorem assumes concrete ordinary and derived isomorphisms together with their generator
and conjugation equations, and concludes only the K-flat computation equation. It does not assert
existence of those isomorphisms or the entire original normalization predicate.

## No longer needed

The assigned module does not need the originally planned direct imports of
`Sheaf.Algebra.Homology.ExtensionTensorComparisonIndependent`, node
`lem-cbc-extension-tensor-comparison-independent`, or
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, node
`lem-pc-kflat-resolution`, or
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, node
`lem-weil-pbc-site-derived-tensor-descent`. The ordinary comparison is constructed from the internal
one instead of a new sectionwise balanced construction. The derived comparison and its conjugation
identity are obtained directly by equivalence cancellation, so no localization descent or
resolution is needed to construct them. The representative compatibility theorem remains a
proof dependency of the smaller computation node. No modules are withdrawn or claimed to be
unused throughout the library. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

The old plan treated localization and essential surjectivity as necessary to construct the
derived comparison. Equivalence cancellation gives that comparison and its conjugation equation
directly, leaving only the representative computation equation. No mathematical statement error
was found. Edge cases checked mathematically include zero coefficients, identity scalar maps and
the empty scheme: equivalence cancellation and the zero generator equations remain valid, and
no flatness or boundedness is imposed on the coefficient map.

## New nodes

`lem-sfb-section-tensor-conjugate-computation` records the representative compatibility equation
for already supplied ordinary and derived comparisons. Its source is the original transport
node's second step; its docstring gives the full counit and tensor localization calculation and
transport along the termwise equivalence. The unit and chapter route are unchanged. The private proof context is
recorded in `coord/changes/R4-section-tensor-proof-context.md`; existing public interfaces
are unchanged.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
