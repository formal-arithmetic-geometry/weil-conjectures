## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientClassicalModule_origin` with its statement
unchanged. Only the assigned Lean module and its node are changed. The proof imports
`Sheaf.AlgebraicGeometry.CoefficientComparisonContinuity`,
`Sheaf.AlgebraicGeometry.CoefficientComparisonPresentationSheafification`, and
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits` and
`Mathlib.CategoryTheory.Sites.Equivalence` privately.

The proof works directly with fixed-scalar module sheaves in the full coefficient
universe. On affine etale stages the Kan-extension unit and the supplied sheafification
comparison make the unit invertible, and the triangle identity makes the counit
invertible. Each affine ind-etale basis object has a presentation at index size u+1.
The source and target restriction cocones are colimits, so the stagewise counit
isomorphisms induce a vertex isomorphism. Dense restriction reflects isomorphisms.
Proved private constant-scalar equivalences and uniqueness of left adjoints transport
this antecedent to the specified intrinsic module pullback. Their constructions follow
the already proved private constructions in `CoefficientComparisonFixedPullback`;
that module is not part of this delivery, and no other existing module is changed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.coefficientClassicalModule_origin`
(node `lem-pe-coefficient-classical-module-origin`). The item originally had one hole;
none remain. No holes added and no split-off statements. This proof uses existing
coefficient-sized continuity and presentation-sheafification declarations; it does not
claim that those dependencies are sorry-free.

Validation: `lcompile.py` compiled the complete assigned module cleanly in 24.5 seconds.

## No longer needed

No existing imports were removed. The original public statement imports are retained.
The previous planned direct dependencies `det-pe-classical-sheaves-image` and
`det-pe-classical-sheaves-modules` and their modules
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage` and
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules` are unnecessary for this proof:
the counit criterion is proved directly in modules, on the coefficient-sized model.
These declarations remain in the library and may have other consumers; no module is
withdrawn. The continuity-map dependency remains, and the node now records the actual
coefficient-sized continuity, sheafification, comparison-data and affine-basis inputs.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cited classical set and fixed-scalar module descent only on
the original sites with coefficients in Type (u+1). Those signatures do not immediately
cover an arbitrary A in Type (max v (u+1)). The direct affine-basis argument above works
at the required universe without a Noetherian hypothesis or a derived-category detour.
The affine-basis node is written for affine bases, but its attached source-library
restriction theorem is stated for every scheme; the proof uses that general signature.
The unit route is preserved; there are no statement or definition changes, consumer
adaptations, new nodes, or change records.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
