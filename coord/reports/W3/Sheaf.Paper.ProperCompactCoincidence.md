## What changed

`WeilConjectures.properCompactCoincidence` keeps its exact statement and now has a
complete assembling proof. The finite natural comparison is constructed by extending
compactification coherence from bounded-below etale origins to the full finite
constructible subcategory, then cancelling extension by zero for the identity open.
The finite sections and cohomology clauses follow by `mapIso`.

The integral comparison is isolated in `ProperCompactIntegralComparisons`; its two
clauses distinguish the recorded natural functor from the independently chosen Roos
image values. The rational functor comparison is proved in
`ProperCompactRationalFunctorComparison` by lifting the integral ambient comparison
through the full subcategory and tensor induction on rational morphisms. The normalized
common-stage action comparison is isolated in
`ProperCompactCoefficientActionComparison`.

All integral, rational and algebraically closed image, sections and cohomology clauses
are assembled in the original module. Rational images are localization of the integral
value isomorphism; algebraically closed images use the input's literal finite stage.
The point-fibre and every degree of cohomology are the recorded functors, applied to
these isomorphisms. No definition, existing declaration signature, public import or
upstream source module is changed.

## Proved and sorry left

Closed the original local hole in `WeilConjectures.properCompactCoincidence` (1 of 1).
Its finite natural comparison and all sections/cohomology deductions are proved.
`WeilConjectures.properCompactRationalFunctorComparison` is proved from the integral
comparison by tensor naturality.

Two holes are added, each in its own module and with its source and complete argument
in the declaration docstring and matching DAG node:

- `WeilConjectures.properCompactIntegralComparisons`:
  `lem-weil-proper-compact-integral-comparisons`.
- `WeilConjectures.properCompactCoefficientActionComparison`:
  `lem-weil-proper-compact-coefficient-action-comparison`.

This is a decomposition, not a completed axiom-free proof of the original theorem:
1 upper hole closed, 2 strictly smaller holes added, net -1 local hole. The original
module has zero local holes; the delivered modules have two in total. Existing
imported declarations may themselves depend on holes; this report does not claim
otherwise. The point Over instance is unchanged and contains no hole.

## No longer needed

Removed the following private proof imports from the original module after writing
the proof: `WeilConjectures.Compactification.Refinement`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`,
`Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`,
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`,
`Sheaf.Paper.CommonStageCompactWeilCohomology`,
`Sheaf.Paper.CompactificationCoherence`,
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
`Sheaf.Paper.QcqsCompactSupportRealization`,
`Sheaf.Paper.SfCommonStageDirectImage`, `Sheaf.Paper.SfRationalizationKaroubi`, and
`Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`. Necessary declarations
remain available from the retained imports. This removes direct redundant imports,
not those modules from the entire targets' closure.

Reviewer correction: the added imports `Sheaf.Paper.FixedEtaleOriginDerivedCategory` and
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact` were unused and are removed.
The finite comparison does not use `prop-compactification-coherence-detailed` or
`def-sf-etale-origin-subcategory`; it uses the canonical transport
`fixedCompactSupportOriginIso` (def-sp-fixed-compact-support-comparison),
`sfIntrinsicCompactSupportComparison` (def-sf-intrinsic-compact-support-realization),
the intrinsic derived equivalence (def-sp-finite-intrinsic-direct-adjunction) and fullness
(lem-weil-pbc-fixed-module-derived-hom-bijection); the item node's proof_deps say so.

The original integral-tower and coefficient-descent nodes are no longer direct
assembly steps: their remaining use is recorded in the respective new intermediate
nodes. Neither is withdrawn. No module is withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed or disputed. The existing finite normalization
interface is bundled in `PurityFiniteSetting`, whereas the target uses the separate
small `Coefficient l Ω E₀` model. The proof therefore constructs its finite
compactification comparison directly from the existing fixed-coefficient etale-origin
and coherence declarations, using the original identity normalization at the end.

The identity-compactification tower theorem alone does not supply a comparison for
arbitrary `c` with the exact completed ordinary functor and independently recorded
Roos values. This interface step is the first split. The coefficient-descent theorem
has explicit normalized tower-induced and scalar-model hypotheses; the second split
retains the missing compatibility step for arbitrary normalized actions rather than
assuming that objectwise isomorphisms imply naturality on common-stage morphisms.
Separate finite evaluations are never treated as faithful.

Edge cases checked in the new statements and arguments: zero inputs, empty schemes,
the identity compactification, identity coefficient stages, and the positive level
`n = 1`. Properness is retained throughout. No finite Tor-amplitude hypothesis is
added. The full unit route (identity compactification, integral passage, rational and
common-stage descent, then point fibre and cohomology) remains intact.

## New nodes

`lem-weil-proper-compact-integral-comparisons` records only the integral natural
functor comparison and identification of its chosen Roos values. It is strictly a
part of the original argument and has no finite, rational, algebraically closed,
sections or cohomology conclusion.

`lem-weil-proper-compact-rational-functor-comparison` records the proved raw tensor
localization of the integral natural comparison. Its Lean proof handles pure tensors,
zero and sums explicitly.

`lem-weil-proper-compact-coefficient-action-comparison` records only compatibility
and descent of the two normalized coefficient actions. Its proof in words identifies
the whole-system scalar squares before descending common-stage representatives.

All three node files are under `dag/nodes/sec-zeta-weil/`, in the original unit
`sk-input-weights`. They inherit the original blueprint source and do not replace its
unit-level statement. There is no definition/statement change record and no forced
adaptation of another group's module.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
