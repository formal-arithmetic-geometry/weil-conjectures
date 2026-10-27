## What changed

Decomposed `AlgebraicGeometry.ProEtale.SpTowerShriek.strictCompactificationComparisonRealization`
without changing its signature or any comparison definition. It now combines coherent
system coordinates, open/word evaluation, and finite word identification. The tensor
reduction clause is discharged by the existing `SemilinearSections.tensor_reduction_formula`.

The bounded-below adjunction clause is proved from the canonical derived-unit factorization
and uniqueness: the restriction of the unbounded adjunction equals `derivedPlus`, and its
unit/counit equations give exactly the required canonical comparisons. The two bounded-below
proofs are in separately named, proved modules so their elaboration is isolated. The proof of the
generic restriction identity follows the existing private argument in
`Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow` (no import of that unrelated
geometric result). The bounded-below evaluation clause is proved by conjugating
`pushEvaluation` with the canonical inclusion comparisons and lifting through the fully
faithful inclusion of D+ into D. Its required equation is map_preimage followed by inverse
cancellation. Neither proof uses faithfulness of evaluation.

Moved existing comparison interfaces verbatim into the publicly reexported
`Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData`, solely to avoid circular
imports between the theorem and its three residual proof steps and the two proved bounded-below clauses. The only changes to the
moved declaration region are blueprint documentation tags. The change record is
`coord/changes/F4-strict-compactification-comparison-interfaces.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpTowerShriek.strictCompactificationComparisonRealization`
(node `lem-sp-strict-compactification-comparison-realization`) by a complete assembly proof.
The original item has zero holes left. This is a decomposition, not a complete proof of
all its mathematics: one hole closed, three lower holes added, net minus two.

Every added hole, each exactly `:= by sorry` in its own public theorem and module:

- `AlgebraicGeometry.ProEtale.SpTowerShriek.strictSystemGeometricRealization`, node
  `lem-sp-strict-system-geometric-realization`: coherent Base/Operations construction,
  extension of the calculus to the published semilinear data, and the two three-index laws.
- `AlgebraicGeometry.ProEtale.SpTowerShriek.strictOpenWordEvaluation`, node
  `lem-sp-strict-open-word-evaluation`: normalized open/finite comparisons and evaluation of
  the complete projection and exchange words, on given coherent system coordinates.
- `AlgebraicGeometry.ProEtale.SpTowerShriek.strictFiniteWordIdentification`, node
  `lem-sp-strict-finite-word-identification`: fixed-scalar finite adjunction coordinates and
  identification of finite projection/exchange, including the exact sheafification-counit,
  K-flat representative and pure-total tensor pins.

Each omits independent substantive clauses of the original theorem. The system theorem
omits tensor reduction, both bounded-below clauses, word evaluations and finite realization;
the open theorem assumes fixed system coordinates and omits bounded-below and scalar
realization; the finite theorem concerns only finite categories and assumes levels.
Their docstrings give full proofs in words and their nodes record sources and dependencies.
No private theorem or definition contains a hole.

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.KInjectiveComputes`: the bounded-below
argument uses canonical right-derived comparison and unit uniqueness, not the multi-clause
K-injective-resolution comparison theorem `lem-sp-kinjective-computes`. Its stale direct
`tool_uses` entry was removed from the parent node.

Removed direct proof imports
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` from the item. The required categorical
facts are provided by the existing canonical comparison imports; separated/quasi-separated
and quasi-compactness facts belong to the finite-word argument, not the assembly.

Removed the direct import `Sheaf.SixFunctors.OpenTensorNormalization` from the assembly;
its theorem is still needed by the residual system/open/finite constructions, recorded in
their proof dependencies. The public import of `OpenTensorNormalizationData` is preserved
through the data module. All eight original public imports are preserved through that
public reexport. `SystemTensorReductionFormula` remains a proof import of the assembly.
The enough-injectives Mathlib import is used there. No source-library declaration or module
is withdrawn, and no whole module is claimed globally pruned. All original mathematical
routes other than the unused K-injective comparison are retained below the new steps.
The unit statement and its realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing plan's bounded-below comparison can be proved
using the canonical inclusion comparisons already in the source library. Evaluation on D+
can be lifted through the fully faithful inclusion; no hypothesis that evaluation preserves
K-injectives is necessary. Existing definitions made independent proof steps circular
unless factored into a shared data module, now done without changing their meaning.

Edge cases checked for the new steps: equal coefficient indices, nonflat quotient maps,
zero derived inputs, empty schemes, identity open squares, ramified extensions, and
independently chosen origin witnesses. No invertibility of a proper projection or exchange,
flatness of coefficient quotients, cartesianness of arbitrary system inputs, or coherence
between distinct origin witnesses is introduced.

## New nodes

`def-sp-strict-compactification-comparison-interfaces` attaches the unchanged existing
comparison declarations to their new data module; it adds no mathematics and has no hole.

`lem-sp-strict-system-geometric-realization` isolates construction and the two three-index
coherences from parent proof steps 1--3. Its proof uses the actual identity-section tower
presentation, semilinear derived sections and scalar/pullback mate pasting.

`lem-sp-strict-open-word-evaluation` isolates parent steps 5--7 on given coherent operations:
open-unit transposes, finite normalized open comparisons, naturality and evaluation of
proper/open compactification words.

`lem-sp-strict-finite-word-identification` isolates the finite scalar presentation part of
parent steps 6--7, retaining the exact underlying sheafification counit and every finite
tensor pin. It uses finite open normalization and the existing compact-support exchange
transport theorem, one witness at a time.

All nodes inherit the parent chapter/unit and ancestor `det-sp-tower-shriek-levels`, proof
paragraph (2). LeanFinder, Loogle and source-grep queries are logged in searches.jsonl;
Mathlib provides the generic tensor and mate tools but no matching normalized tower
comparison. Blueprint searches found no duplicate statement.

The shared DAG has pre-existing deep missing-reference/cycle issues below adopted
dependencies (for example the mutual ring-Hom differential/adjacent nodes). This packet
introduces no direct missing node, and its new nodes point only to the factored interfaces
and the original parent dependencies; they do not point back to the original theorem.

The bounded-below adjunction and evaluation modules add proved nodes
`lem-sp-strict-plus-comparisons-realization` and
`lem-sp-strict-plus-evaluation-realization`; neither adds a hole. Finite-level enough
injectives is obtained by transporting to `proEtaleSiteModel`, applying the small-site
Grothendieck theorem, and transferring back along a proved private copy of the source module equivalence construction (the source helper is private).

Validation: all seven delivered modules compile via `lcompile.py`; the final assembly
compiled in 11.8 seconds after pinning the enough-injectives universes. The
moved declaration region and original theorem signature were compared byte for byte
(after the documented blueprint-tag substitution) and match. All Lean lines are at
most 100 characters. No current consumer requires a forced adaptation.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
