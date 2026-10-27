## What changed

Prove `CategoryTheory.CoefficientStageDescent.texact_coefficient_stage_descent` in
`Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent`. Private helpers construct
its canonical comparison package, prove exactness of the actual heart restriction,
transport exactness and t-exactness through the supplied localization factorization,
and descend the specified shift comparison through the existing StageSystem quotient.
The beta, associator, inclusion and transition squares use the proved truncation and
cohomology comparison APIs. The stage-system argument is proved in a private generic
helper before specializing to coefficient localizations, keeping coefficient-instance
unfolding out of its proof. The existing theorem signature, definitions, structures
and public imports are retained. Update the theorem node's proof route accordingly.

## Proved and sorry left

Original hole: `CategoryTheory.CoefficientStageDescent.texact_coefficient_stage_descent`
(node `lem-a1-texact-coefficient-stage-descent`). The delivered source has a complete
proof and zero textual holes. No holes added and no intermediate statement split off.
The complete module compiled without warnings in 32.0 seconds.
`#print axioms texact_coefficient_stage_descent` returned only `propext`,
`Classical.choice` and `Quot.sound`. Final delivery checks are recorded by the tool.
The proof-context change record is
`coord/changes/C6-coefficient-descent-proof-elaboration.md`.

## No longer needed

The declared dependencies `lem-pur-semilinear-scalar-localization` and
`lem-a1-texact-pair-descent` are unnecessary for this proof. The fraction extension
and its shift-compatible factorization are already hypotheses, so constructing and
identifying another extension is redundant. The actual StageSystem quotient already
provides the functor, its action on representatives, the induced pair shifts and the
finite-stage triangle presentation; rebuilding those via ExactPairDiagram and
ExactPairPresentation is unnecessary. Their modules are not imported. The unused private imports
`Mathlib.LinearAlgebra.TensorProduct.Tower` and `Mathlib.Algebra.Colimit.Module` are removed.

Keep `lem-weil-heart-short-exact-triangles`, `lem-pod-texact-truncation-comparison`,
`lem-a1-cohomology-comparison-pasting` and the t-structure definitions. No module is
withdrawn, and no source-library declaration is removed. The unit's own statement and
steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned construction and uniqueness of a semilinear extension repeats supplied
FractionExtension data. The planned pair-descent application uses a separate generic
presentation whereas this statement is about the existing StageSystem category.
The direct proof uses that category's already available representative calculus.

Several hypotheses are stronger than needed by this Lean conclusion (including the
integral boundedness and explicit unit hypotheses). They are retained verbatim.
The canonical inclusion comparisons already respect the canonical maps, and their
uniqueness identifies any supplied TruncationsComputedAt witness with them, so that
witness need not be chosen in the proof. No arbitrary object is chosen from an
unproved mere existence statement.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
