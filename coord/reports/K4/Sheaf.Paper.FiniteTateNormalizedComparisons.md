## What changed

Restored `Sheaf.Paper.FiniteTateNormalizedComparisons` from its recorded quarantine
archive, preserving its declaration and statement. Replaced its whole-proof hole
by degree-one assembly followed by a two-step induction on the tensor exponent.
The degree-one proof composes the existing finite-root site comparison with the
inverse fixed-scalar root presentation. The equality of actual units is used to
identify finite roots through the monic inclusion. The zero and tensor steps use
the monoidal comparison adjunction, including restriction to arbitrary pro-etale
tests. No etale lift of an infinite root tower is assumed.

Added `Sheaf.AlgebraicGeometry.ComparisonPureSections` for the ordinary monoidal
adjunction section equations. Added
`Sheaf.CategoryTheory.ConstantScalarExplicitTensor`, which proves normalized
unit and tensor comparisons for the actual explicit site tensor, from the existing
ordinary constant scalar restriction theorem and module sheafification. Added
`Sheaf.Paper.FiniteTateRootTensorPresentation`, isolating the remaining comparison
on the pro-etale site alone. Updated the item's proof route and supplied nodes for
the new modules. No existing shared interface or target statement changes.

## Proved and sorry left

Closed the textual hole in
`AlgebraicGeometry.Scheme.finite_tate_normalized_comparisons`, combining the
first-degree normalization, monoidal unit and tensor section formulas, and
induction into the unchanged family statement.

Proved `CategoryTheory.ConstantScalarRestriction.explicit_tensor_comparisons`
and `AlgebraicGeometry.Scheme.comparison_pure_sections`.

Added one hole:
`AlgebraicGeometry.Scheme.finite_tate_root_tensor_presentation`
(`lem-amb-finite-tate-root-tensor-presentation`). Its statement concerns only the
first pro-etale twist and its projection to finite roots. It has no etale-site
comparison or higher-power conclusion, so it is a strict step of the original
argument. Its docstring and node give the scalar-balancing and root-projection
proof. This is a decomposition, with one original hole replaced by one smaller
hole; it is not reported as a net hole closure. The item itself has zero holes;
the delivery has one hole in total. There are no holed definitions. All four modules compile through `lcompile.py`;
the final delivery performs the independent compile and preflight checks.

Edge cases checked mathematically: the empty scheme, degree zero (empty tuples),
degree one, arbitrary positive annihilating exponent, and ramified coefficient
quotients not flat over Z/l^(r+1). The generic scalar tensor statement also allows
the zero ring and empty site.

## No longer needed

The item's direct proof import of `Sheaf.Paper.AmbTateRootProjectionReduction` is
replaced by the smaller fixed-scalar presentation interface. Root projection is
still a proof dependency of that new node and is not withdrawn or declared
unnecessary. The direct import of
`Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` is replaced by
`Sheaf.CategoryTheory.ConstantScalarExplicitTensor`, which uses its ordinary API.
The existing finite-root site comparison remains used through the presentation
module's necessary public import; its redundant direct import in the item is
removed. The split module has no
proof imports: its proposed root-projection and scalar-restriction prerequisites
remain in its DAG proof dependencies. The temporary proof import of
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients` is also unnecessary:
the generic comparison constructs the presentation directly by sheafification.
The section-formula module uses the comparison monoidal module’s public
reexport of the pushforward formulas, so no redundant direct import remains.

The original proof-plan dependencies
`lem-weil-pbc-ringed-topoi-module-pullback-tensor` and
`lem-sf-comparison-pullback-exact` are unnecessary for this assembly: the existing
strong monoidal comparison inverse image and its monoidal adjunction give the
needed ordinary unit/tensor section equations directly. No exactness or derived
pullback result is used. No existing module or declaration is withdrawn, and the
unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The item source was initially absent from `lean/`, but its rework row identifies
the preserved quarantine archive. This absence did not mean that its declaration
or dependencies could be deleted. The archive was restored, and the original
Lean attachment is preserved.

The earlier single proof step hid two changes of tensor presentation: constant
scalar restriction versus the explicit site tensor, and the first finite twist
versus the fixed finite-root tensor. The former is now proved explicitly, and
the latter is the sole remaining named obligation. No mathematical statement
was found false or weakened.

## New nodes

`lem-amb-comparison-pure-sections` records the proved ordinary tensor and unit
section formulas. Its module isolates these generic site formulas from the
finite-coefficient instance environment.

`lem-amb-constant-scalar-explicit-tensor` records the proved comparison between
fixed-coefficient tensors and the explicit sheafified site tensor, including the
constant-scalar unit formula. It is a generic tool below the existing unit route.

`lem-amb-finite-tate-root-tensor-presentation` records the remaining first-degree
pro-etale scalar presentation and its exact projection formula. The existing
root-projection and constant scalar restriction nodes remain its dependencies.
No change records are needed because all existing public statements and public
imports are unchanged.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
