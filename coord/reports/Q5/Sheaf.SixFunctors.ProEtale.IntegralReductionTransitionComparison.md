## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.IntegralPresentation.integral_completion_transition_comparison`.
The existing theorem signature and both public imports are preserved verbatim.
All new helpers are private and proved. The proof imports existing results on normalized
DVR transitions, the proved K-flat unit helper in normalized DVR effectivity,
legacy representative comparisons, regular quotient projections, and
composition of exact derived squares. No source-library module is changed.

The proof lifts the finite restriction square through fully faithful ordinary restriction,
derives its compositor equation, identifies the section transition by its K-flat
characterization, and transposes the finite transition comparison through the derived
scalar adjunction. The supplied unit equations identify the transposes. The node's
proof, proof dependencies and proof origin now describe this argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.IntegralPresentation.integral_completion_transition_comparison`
(node `lem-pe-integral-reduction-transition-comparison`), the item's one original hole.
Added: no holes, no split statements, no new public declarations.
Remaining in the item: none.

Validation: the complete proof compiled through `lcompile.py` with zero holes.
The proof also covers arbitrary unbounded complexes, the zero object, natural level zero,
and the empty scheme; no extra hypotheses were introduced.

## No longer needed

No existing public import or module is removed. An unused direct proof import of
`Sheaf.SixFunctors.ProEtale.DerivedCompletion` was removed during cleanup; it is already
available through the encoding. The normalized DVR transition import needs only its public API. The following original direct proof
requirements are unnecessary for this proof:

- `lem-stage3-inverse-mate-equivalences` / `WeilConjectures.CategoryTheory.InverseMateEquivalence`:
  no inverse-mate isomorphism theorem is needed; the finite square is lifted by ordinary
  full faithfulness and the given derived comparisons are used directly.
- `lem-pe-internal-section-tensor-comparison` /
  `Sheaf.CategoryTheory.InternalSectionTensorComparison`: no transport of K-flatness
  through the integral section equivalence is needed. Its existing public import through
  the encoding remains because it defines that encoding.
- `lem-pur-derived-change-of-rings` / `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`,
  `lem-pc-kflat-resolution` / `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
  and `def-pur-sheaf-tensor-product` /
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: no new representative,
  tensor balancing calculation, or resolution construction is performed here. The existing
  normalized DVR K-flat transition theorem supplies the representative calculation.
  These modules can still be transitive dependencies and are not withdrawn.

The existing normalized DVR, regular quotient, exact-square composition, and legacy
comparison lemmas are used as tools from their respective units. They supply restriction
full faithfulness, exact localization coherence, and a previously proved transition
calculation; they do not replace the integral criterion's unit statement or route.
No `tool_uses` approvals are added by this packet.

## Where the brief, the DAG or earlier work was wrong

The original plan required transporting internal K-flat resolutions through the section
encoding and identifying tensor maps there. That work is unnecessary: ordinary full
faithfulness lifts the finite square, and the normalized scalar adjunction's Hom bijection
proves transition compatibility. In particular, the ordinary identity-on-sections hypothesis
is unused; it remains unchanged in the public statement. The argument retains arbitrary
unbounded complexes, level zero in the natural indexing, and the empty scheme.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
