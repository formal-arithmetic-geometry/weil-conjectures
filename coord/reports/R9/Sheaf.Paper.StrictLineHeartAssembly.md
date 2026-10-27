## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.SpStrictLineHeart.strict_line_heart_assembly`
with the concentration, normalized heart identification, fully faithful level lifting,
strict tower assembly, uniqueness and prescribed-evaluation argument. The original public
signature and all eight existing definitions are unchanged.

Added `Sheaf.Paper.StrictLineHeartReduction` for the one remaining scalar-adjunction
calculation: a canonical derived reduction square between shifted single objects implies
the actual strict semilinear transition equation. This is only steps 3--4 of the original
argument. It assumes sheaf maps already exist and says nothing about concentration,
heart normalization, invertibility, tower isomorphism construction or final evaluations.
Updated the original node's proof route and added the intermediate node.

The new statement also permits arbitrary sheaf maps and nonflat coefficients. Its proof
transposes reductions using the normalized derived adjunction; the universal comparison
is composed with but never inverted. Small cases checked in words: zero objects and zero
maps; equal coefficient levels; shift zero and negative shifts; the empty scheme; and the
nonflat quotient Z/l² to F_l. Each reduces to the ordinary transition square under the
faithful single embedding.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.SpStrictLineHeart.strict_line_heart_assembly`
(node `lem-sp-strict-line-heart-assembly`), by a complete proof from the new intermediate.
The private helpers `concentration`, `normalized_identification` and
`evaluation_naturality` have complete proofs. The item compiled without warnings in
40.6 seconds before the final direct-import cleanup; the delivery tool checks the final
packet again. All edits are in this item's sandbox; no scratch Lean modules were made.

Added one hole:
`AlgebraicGeometry.ProEtale.shifted_single_reduction_detects_transition`
(node `lem-sp-shifted-single-reduction-detects-transition`), the sole theorem of the new
module. There are no holes in the item module and one hole in the delivery. This is a
one-for-one decomposition, with net zero holes closed, not a claim of a sorry-free proof.

## No longer needed

Replaced `Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence` by
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, the module
actually supplying the individual canonical homology comparison.

Removed these proof-only imports from the item:

- `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars`:
  `lem-sfb-locally-free-derived-scalars` is unnecessary because transposing the canonical
  reduction never requires inverting the derived scalar comparison.
- `Sheaf.Paper.SemilinearSystemModels`: `def-coef-semilinear-system-models` is unnecessary;
  the supplied datum A already carries normalized scalar adjunctions and reductions.
- `Sheaf.Algebra.Homology.SheafRingDerivedHomComparison` and
  `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`: the recorded scalar
  model already includes their normalized cochain transpose and ordinary adjunction.

The original node no longer directly needs `lem-pur-system-level-left-extension`:
componentwise zero detection follows from strict morphism extensionality and faithfulness
of A.equivalence.functor. It no longer needs the coherence theorem
`lem-pur-exact-derived-cohomology-coherence`: the individual canonical homology comparison
suffices, with no comparison of composites. Shift compatibility is now a dependency of
the strictly smaller intermediate. The original scalar-extension functor node is not
used by the proof, although its pre-existing public import is retained.

Pruned the original node's obsolete tool approvals for
`lem-pur-system-level-left-extension`, `lem-pur-exact-derived-cohomology-coherence`,
`lem-sfb-locally-free-derived-scalars`, `lem-pur-sheaf-ring-derived-hom-comparison` and
`lem-pur-sheaf-ring-coefficient-ordinary-adjunction`. No module is withdrawn, no source
library declaration is removed, and no claim is made that these modules have no other
consumers. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan unnecessarily invoked local freeness to invert the scalar comparison.
The reduction-to-transition implication instead uses the normalized scalar adjunction
without inverting that comparison. The original theorem's line and cartesianness
hypotheses remain verbatim; they need not be used by this more general implication.

The compilation environment required explicit site/coefficient universes for the
levelwise fully faithful functor. Functor map lemmas are qualified to avoid the opened
Opposite namespace's unrelated `Functor`. The exact derived functor is locally marked
irreducible in the proof section to avoid expanding localization constructions.

## New nodes

`lem-sp-shifted-single-reduction-detects-transition`, in the item's chapter and unit,
is the scalar-adjunction and shift calculation for arbitrary already-given level sheaf
maps. Its statement is strictly only the compatibility step; its source, detailed proof,
existing dependencies, three kinds of search and Lean attachment are recorded. It does
not assume or conclude the original theorem under a different name. No change record
is needed because existing statements, definitions and public imports are unchanged.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
