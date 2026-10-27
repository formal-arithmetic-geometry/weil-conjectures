## What changed

Replaced the body of `WeilConjectures.IntegralLineReduction.integral_line_derived_comparisons`
by a complete assembly of normalized derived comparisons and a proved support-preservation
lemma. Its signature and original public import are unchanged.

Added `Sheaf.Paper.IntegralLineSupportPreservation`, with a complete proof of
`finite_ordinary_support_subset`. Private proved helpers show that finite signed powers
have rank one and that tensoring with a flat degree-zero sheaf preserves vanishing of
individual cohomology objects in the actual chosen closed tensor model. The latter proof
uses a K-flat resolution, the total-tensor/single collapse, exact-functor homology and
explicit transport through the model's representative isomorphism. It applies to
unbounded complexes and assumes no completeness or constructibility.

Added `Sheaf.Paper.IntegralLineNormalizedDerivedComparisons` for the remaining normalized
comparison clause. This is the first argument of the original node, with the entire
support argument removed; its source and proof in words are recorded in the theorem
and node. Updated the original node to match the assembly.

## Proved and sorry left

Original direct holes: one. The original declaration
`WeilConjectures.IntegralLineReduction.integral_line_derived_comparisons` now has a complete
proof from named statements. The new theorem
`WeilConjectures.IntegralLineReduction.finite_ordinary_support_subset` and its two private
helpers are proved with zero local holes.

One hole added and remaining:
`WeilConjectures.IntegralLineReduction.integral_line_normalized_derived_comparisons`
(node `lem-pur-integral-line-normalized-derived-comparisons`). Its exact proof is
`by sorry` in its own new module. It contains only the comparison, chain/representative
normalization and quotient-transition argument, with no support clause.

This is a decomposition: one original hole closed and one strictly smaller hole added,
net zero direct holes. The finite-line support argument is proved; the delivery does
not claim to have proved the normalized scalar comparison clause. No definition or
private declaration contains a hole. Existing dependent theorem holes are not modified.

Validation: all three Lean modules compiled successfully together on the project server
with no warnings. The original module and support module contain zero direct holes;
the normalized-comparison module contains exactly one. Delivery preflight follows.

## No longer needed

No original import was removed and no module is withdrawn. The original item imported
only its definition module; the two additions are proof-only imports.

The original item's direct use of `lem-pur-line-unbounded-derived-tensor` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is replaced by the two new statements.
Both remain needed below: line flatness is used by the proved support lemma, and the
canonical ringed-topos pullback remains in the proof plan of the remaining comparison
lemma. They are not claimed pruned from the target closure. Cohomological support stays
needed. No unit route is bypassed.

Removed the exploratory proof import `Sheaf.Paper.ScalarExtensionDualTowerCore` from the
new support module, replacing it with the smaller `Sheaf.Paper.ScalarExtensionDualLocalIso`.
The tower coherence API is unnecessary for preservation of rank one by a single scalar
extension. The normalized-comparison module imports only the definitions needed by its
statement, pending implementation of its separate argument.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is sound. The finite closed tensor model need not be identified
with the separate tensor model used by the generic line theorem: its own representative
isomorphism and the flat-single collapse suffice. This avoids a further model-comparison
obligation. The combined theorem preserves the original interval endpoints exactly.

The new support statement covers signed exponent zero, positive and negative exponents,
quotient index zero (the first positive quotient power), arbitrary cohomology degrees,
and unbounded complexes. Rank-one scalar extension and exactness do not require a
nonempty scheme or a nonzero quotient ring. The remaining comparison statement retains
all original representative and transition clauses and has no extra assumptions.

## New nodes

`lem-pur-integral-line-support-preservation`, in
`dag/nodes/sec-smooth-purity/lem-pur-integral-line-support-preservation.json`, records the
proved finite-line support inclusion. It is strictly the support step of the original
argument, generalized to an arbitrary finite derived input.

`lem-pur-integral-line-normalized-derived-comparisons`, in
`dag/nodes/sec-smooth-purity/lem-pur-integral-line-normalized-derived-comparisons.json`,
records the remaining natural comparison and its simultaneous chain, counit and transition
normalizations. This is a strict part of the original theorem; the support proof is
implemented separately and combined in Lean. No existing definition, signature or source
library declaration changed, so no change record is required.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
