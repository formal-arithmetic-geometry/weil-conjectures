## What changed

Filled all eight theorem proofs in `Sheaf.Paper.CompletedCoefficientPullbackLinearity`.
The scalar-square proof first computes every actual quotient projection, then uses
constant inverse-image naturality and the sheaf adjunction to obtain the adjunct
square and its equation on constant sections. Direct-image linearity is proved on
sections; the specified module adjunction transfers it to the left adjoint.

Exactness uses the existing `pbcIsoModulePullback_eq_completed` identification and
`pbcIsoModulePullback_isEquivalence`. The actual module adjunction makes direct image
an equivalence as well. Mathlib supplies exact derived linearity. Its transfer along
`pbcIsoOrdinaryDerivedComparison` proves ordinary K-flat pullback linearity.
The automorphism-completion theorem is applied to the actual target representative,
realized through that comparison; its unit equation proves completeness. The final
functor is `ObjectProperty.lift`, with the stated inclusion equality by reflexivity.

Added the proof import `Sheaf.Paper.AutomorphismCompletionUnitComparison` and updated
the existing node's proof route and dependencies. All existing signatures, public
imports, definitions and exported instances are preserved. No consumer adaptation
or change record is required. The added dependency
`def-wf-automorphism-completed-transport` is an existing generic normalized transport
comparison; the unit has no prescribed proof steps, and no unit route is bypassed.

Validation: the remote single-file compile passed in 6.1 seconds, with no errors
or warnings. All eight theorem signatures and every public import were compared
with the original and are identical. The new dependency was checked for both
Lean import cycles and DAG cycles.

## Proved and sorry left

Closed eight of eight original holes:

- `AlgebraicGeometry.Scheme.sfCompletedCoefficientScalarSquares`.
- `AlgebraicGeometry.Scheme.sfCompletedModulePullback_preservesFiniteLimits`.
- `AlgebraicGeometry.Scheme.sfCompletedModulePullback_preservesFiniteColimits`.
- `AlgebraicGeometry.Scheme.sfCompletedModuleDirectImage_preservesFiniteLimits`.
- `AlgebraicGeometry.Scheme.sfCompletedModuleDirectImage_preservesFiniteColimits`.
- `AlgebraicGeometry.Scheme.sfCompletedCoefficientPullbackLinearity`.
- `AlgebraicGeometry.Scheme.sfCompletedCoefficientPullback_preservesComplete`.
- `AlgebraicGeometry.Scheme.sfCompletedCoefficientCompletePullback_linearity`.

All realize `lem-sf-completed-coefficient-pullback-linearity`. No local holes remain,
no holes are added, and no statements are split off. These proofs use the existing
stated dependencies, including the still-open automorphism transport and completion
comparison statements; this is not a claim that the transitive closure is sorry-free.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.RingedPresentationTransport`: exactness follows from the
  already stated equality with automorphism module transport and its equivalence.
- `Sheaf.CategoryTheory.RingedDerivedPullbackLinear`: for this automorphism, ordinary
  pullback is isomorphic to exact derived transport, whose linearity follows from
  module linearity and Mathlib's exact derived functor instance.

Accordingly the direct proof dependencies
`lem-weil-pbc-ringed-presentation-transport`,
`lem-pur-ringed-derived-pullback-linear`, and
`lem-weil-pbc-ringed-topoi-derived-pullback` are not used by this proof. The latter's
existing public import stays as part of this module's public interface. No assertion
is made that these nodes or modules are globally unused; other consumers retain them.
The direct dependency `lem-weil-proetale-isomorphism-inverse-image` is also
unnecessary: the proved coefficient-naturality lemma holds for arbitrary morphisms,
and exactness comes from the existing automorphism-transport interface. Its public
import remains. The three obsolete top-level tool approvals are removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned reconstruction of exactness and separate
K-flat linearity argument are unnecessary: the existing normalized automorphism
transport comparisons already give both. The original completion plan mentioned
representative independence; the proof instead feeds the actual target representative
into the comparison theorem, with its realization composed with the ordinary/exact
comparison. The explicit intrinsic-unit formula then transfers invertibility.

Edge cases require no additional assumptions: the proof uses no nonzero scalar,
nonempty scheme, positive tuple length, boundedness or constructibility condition.
Thus identity automorphisms, zero coefficients, empty schemes and empty generating
tuples are all covered by the same argument.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
