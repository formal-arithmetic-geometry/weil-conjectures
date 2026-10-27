## What changed

Replaced the original combined proof hole by a proof assembled from independent universal,
section and scalar-model comparison steps. The computation-unit part of section coherence
is proved directly from the existing right-derived comparison equation. Model-map naturality
is handled separately using computation units and natural transformations. The scalar-unit
case is a specialization of the same argument to the actual derived scalar-unit morphism.
The original theorem signature, public import and all definitions are preserved.

## Proved and sorry left

The original hole is
`AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence.closed_test_scalar_model_coherence`.
Its assembly proof is complete. This is a decomposition, not a claim to have proved the
scalar comparison theory without additional holes.

Closed 1 original hole by decomposition; added 4 strictly smaller holes.

New remaining holes (their nodes are listed in the same order):
`lem-sfb-closed-test-scalar-universal-coherence`,
`lem-sfb-closed-test-scalar-section-squares`,
`lem-sfb-closed-test-scalar-model-squares`,
`lem-sfb-closed-test-chain-model-map-naturality`.

- `AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence.closed_test_scalar_universal_coherence`.
- `AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence.closed_test_scalar_section_squares`.
- `AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence.closed_test_scalar_model_squares`.
- `AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence.closed_test_chain_model_map_naturality`.

The supporting theorem `closed_test_scalar_section_coherence` has a complete proof from
`closed_test_scalar_section_squares` and the universal computation-unit equation.
The separate `closed_test_model_map_naturality` proves the source, target and two
localization naturality squares from natural transformations on complexes and uses
`closed_test_chain_model_map_naturality` for the remaining chain square.
Each remaining hole is a public named theorem in a separate new module with a source,
proof in words and matching node. No definition contains a hole.

## No longer needed

Removed private imports from the item module:
`Sheaf.CategoryTheory.ExactSquareRightDerivedUnit`,
`Sheaf.CategoryTheory.InternalSectionScalarAdjunction`,
`Sheaf.Paper.SectionDerivedPushpullNormalization`,
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`,
`Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`,
`Sheaf.Paper.ClosedTestUnitEvaluation`,
`Sheaf.Paper.RingedDerivedSliceLocalization`, and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
Their relevant mathematical dependencies remain recorded on the split proof steps;
this is not a claim that all those modules have become globally unused.
K-injective representability is imported privately by the model-map proof.

The model-map proof uses computation-unit naturality directly rather than importing
`Sheaf.Paper.ClosedTestLocalizedModelCoherence` and transporting its different model
presentation. The declared proof dependency `lem-sfb-closed-test-localized-model-coherence` is not
needed: the four comparison squares follow from ordinary natural transformations,
and the chain square is isolated as its own representative calculation.
The declared dependency `lem-weil-pbc-ringed-derived-slice-localization` is also not
needed by these predicates: localizationModel uses derived sections on a test, whose
coefficient square follows directly from its degreewise section identity. The stronger
pushforward-on-slices comparison is absent from the displayed conclusions. Its obsolete
top-level `tool_uses` entry is removed, preserving the order of the remaining approvals.
Neither node or module is claimed globally unused.

No existing module is withdrawn. In particular, the unfinished parent
`lem-sfb-closed-test-derived-exchange-model` still needs the original item, so zero current
Lean importers does not justify pruning it.

## Where the brief, the DAG or earlier work was wrong

Edge cases checked for the new statements: the identity coefficient map gives identity
scalar comparisons; the zero coefficient ring still gives forward arrows with no
invertibility claim; the zero and unit ideals give respectively the identity and empty
closed test; non-flat coefficient changes do not require preservation of K-injectives.
Model-map naturality permits zero objects, identity and zero arrows, and arbitrary changes
of K-injective representatives; its argument uses only naturality and isomorphism
cancellation, so does not impose hidden boundedness or flatness conditions.

The attempted direct chain-square calculation is left as a genuine separate step at the
first delivery point. Large inferred natural-transformation types were bounded by explicit
types and irreducible private definitions; a looping forward/backward map-composition
simplification was replaced by directed rewrites. No shared definition was changed.

No false statement was identified. Existing model-comparison declarations use a different
presentation from the eight specified isomorphisms and five squares of this item. Applying
them requires transport through the explicit universal computation units; the new statements
make the remaining scalar comparison obligations explicit. The original nine-step plan is
retained mathematically, with the independent parts separated and the final map clauses
assembled by naturality. No source-library declaration or target statement is changed.

## New nodes

- `lem-sfb-closed-test-scalar-universal-coherence`: the five universal scalar comparison equations.
- `lem-sfb-closed-test-scalar-section-squares`: ordinary, derived and push-evaluation section squares.
- `lem-sfb-closed-test-scalar-section-coherence`: the proved computation-unit assembly.
- `lem-sfb-closed-test-scalar-model-squares`: model isomorphisms and scalar squares, assuming
  the preceding universal and section coherence.
- `lem-sfb-closed-test-model-map-naturality`: four proved naturality squares and assembly
  with chain naturality for two independently supplied models.
- `lem-sfb-closed-test-chain-model-map-naturality`: only the chain square, by the explicit
  rightDerivedPullback representative formula and derivedSectionArrow naturality.

The parent node's proof, proof dependencies and proof origin follow the new assembly.
The supporting chain/model modules were accepted by the full sandbox compiler and the
delivery compiler. The final section wrapper and main assembly are checked by delivery
preflight; all compilation is through the supplied project tools.

Change record: `coord/changes/S9-closed-test-scalar-coherence-decomposition.md`.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
