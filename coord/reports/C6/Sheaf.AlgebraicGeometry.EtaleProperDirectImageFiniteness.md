## What changed

Proved `AlgebraicGeometry.Etale.proper_directImage_finiteness` in
`Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness`, with its complete signature
and all public imports unchanged. No definitions or other modules changed.

Constructibility applies the declared compactification theorem to `F[0]` and
`Compactification.ofIsProper f`. The proof explicitly removes identity extension by zero
using the identity pullback comparison and its exact derived functor, then transports
homology from total to bounded-below right derived direct image. Finite-value module
constructibility is transported through the proved equivalence with constructible sheaves;
all nonzero degrees of `F[0]` are zero by the standard t-structure.

Vanishing uses `isIso_geometricFiber_finite` at exactly `Y.algClosurePoint y`, the
points appearing in the hypothesis. Exact pullback commutes with homology and with the
single functor. The source-library theorem
`isZero_higherDirectImage_of_two_mul_lt` makes the fibre direct image zero using the
given dimension bound and additive torsion of the finite ring. The proved
`isZero_of_forall_isZero_upperStar_algClosurePoint` detects zero on Y.
This route needs neither the global dimension bounds nor the coefficient invertibility
hypothesis, which are retained and explicitly cleared. It covers empty X, empty Y,
empty fibres, e=0, the zero ring, and every integer q>2e without excluding cases.

Added proof imports:

- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`
- `WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp`
- `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`

Updated the item's DAG proof, proof dependencies and proof origin to this argument.
The existing node `lem-kun-relative-torsion-direct-image-dimension-bound` is used as a
general tool: its existing source-library theorem is exactly the fibre calculation needed
here and avoids rebuilding the abelian-coefficient argument. The constructibility
comparison is the proved node
`lem-weil-pbc-constructible-etale-module-sheaf-comparison`. The compactification is the
existing `def-nagata-compactification`, not the pro-etale ring-valued functor currently
attached to `def-weil-pbc-projection-compactification`. No unit statement or realized
unit proof step is bypassed.

Searches: launcher `leanfinder` returned eight unrelated scheme constructible-image
results; `loogle` for `"higherDirectImage"` and launcher `grep` found no Mathlib match.
Direct rg in both library roots found the existing torsion-module vanishing theorem;
the field-base proper-constructibility theorem is inapplicable to an arbitrary Noetherian Y.
Sources read: Stacks etale-cohomology.tex, lemma-cohomological-dimension-proper (095U),
and more-etale.tex, theorem-constructible-shriek (0GL0).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.proper_directImage_finiteness`
(node `lem-weil-pbc-etale-proper-direct-image-finiteness`).

Added 0 holes; split off 0 theorems. There are no remaining `sorry` declarations in the
assigned module or added modules. This is a proof from existing declared dependencies,
not a decomposition. The imported compactification-constructibility theorem and
geometric-fibre base-change theorem still have their pre-existing obligations;
this delivery adds no replacement or duplicate for either.

Validation: the full proof compiled after removing the twelve imports below. The final
warning-free compile and the delivery dry run are recorded by the delivery tool,
including its declaration/axiom probe.

## No longer needed

Removed these twelve proof imports from this module:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
- `Sheaf.AlgebraicGeometry.GeometricPointCohomology`
- `Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`

The following planned proof dependencies are no longer used directly by this theorem:

- `lem-sc-affine-noetherian-underlying-space`
- `def-weil-pbc-projection-compactification`
- `lem-sf-separably-closed-torsion-cd`
- `thm-sc-finite-type-torsion-cd`
- `def-sc-etale-torsion-cd`
- `lem-weil-pbc-etale-module-cohomology-forget`
- `lem-sc-fibre-dimension-after-base-change`
- `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`
- `lem-weil-pbc-geometric-point-cohomology`
- `prop-weil-pbc-geometric-stalks-exact`
- `lem-sbc-higher-direct-image-forget-comparison`

The relative torsion-module vanishing theorem packages the finite-type torsion bound
and coefficient comparisons. Using only the chosen algebraic-closure points eliminates
the arbitrary-overfield embedding and fibre-dimension transport. Module pullback and
homology comparisons eliminate the separate geometric-point sections/stalk calculation.
These dependencies may remain used inside the existing library inputs or by other
parents; no globally unreachable module is claimed without the maintainer's census.
The obsolete top-level tool approvals for the first seven removed tools were withdrawn;
`lem-sp-exact-functor-preserves-homology` remains, since the proof uses exact pullback's
homology comparison. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned vanishing argument
was longer than necessary given the already proved source-library torsion-module bound.
Its reduction to arbitrary geometric overfields and abelian cohomology is unnecessary
because canonical algebraic-closure pullbacks already detect zero. The old projection
compactification attachment describes a pro-etale ring-valued image; the proof instead
uses the existing scheme compactification structure and its proper identity construction.
No new definition, statement repair, change record or consumer adaptation is required.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
