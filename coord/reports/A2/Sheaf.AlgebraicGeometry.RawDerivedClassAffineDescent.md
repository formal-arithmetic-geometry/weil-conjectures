## What changed

Proved `AlgebraicGeometry.Etale.exists_rawDerivedClass_affine_descent` without
changing its signature. Restrict to `Over i`, descend the affine etale chart,
construct the actual pullback diagram over its model stage, and prove its cone
limiting using `Over.pullback` and pullback symmetry. Derived cohomology continuity
and joint surjectivity of the underlying type colimit supply a stage class.
Canonical raw evaluation converts it to the required raw derived morphism.

Added `RawFixedDerivedComparison`, `RawFixedDerivedComparisonIsIso`, and
`RawFixedDerivedComparisonNaturality`.
The comparison is explicitly constructed from existing raw evaluation and
inverse-image composition. Its invertibility and its compatibility with the
canonical `presentationDerivedMap` are proved. The latter uses the existing
restricted-section shift transport and generic derived composition coherence;
it has no geometric limit hypotheses and applies to every integer degree.

Aligned the free-sheaf abbreviation in the existing, unclaimed
`RawRestrictedDerivedComparisonPullback.rawRestrictedDerivedPullback` with the
canonical `abelianComparisonFree` used by the chart API. The two expressions
are definitionally equal. This controls repeated kernel unfolding in the final
transport identity. Its naturality theorem uses the same canonical spelling in
its source binder and local free-sheaf abbreviations; its proposition is
definitionally unchanged.
See `coord/changes/raw-derived-pullback-canonical-free.md`.

Single-file checks: the item compiles cleanly in 37.3 seconds; the new comparison
and naturality modules compile cleanly, as does the adjusted raw-pullback module.
The existing downstream `CartesianPresentationShiftCoherence` compiles unchanged
against the adjusted dependency (3.0 seconds).

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Etale.exists_rawDerivedClass_affine_descent`.
One of one original holes closed; zero holes added or split off.

The new theorems
`AlgebraicGeometry.Etale.isIso_rawFixedDerivedComparison` and
`AlgebraicGeometry.Etale.rawFixedDerivedComparison_naturality` are also proved.
All private helpers are proved. No delivered declaration contains `sorry`.
The raw comparison is explicit data; the finite-stage class is selected only
inside a theorem proving existence, never inside a definition.

The comparison and naturality statements include empty charts, zero coefficients,
identity pullbacks, and all integer degrees. Affine descent includes q=0 and the
empty affine etale chart by the same limiting-cone and colimit argument.

## No longer needed

No original import, node, or module is pruned. The proof uses the intended
finite-presentation descent and fixed-coefficient continuity route. The second reader replaced the new comparison module’s import of
`AbelianFreeRepresentablePullback` by its narrower dependency
`AbelianHigherDirectImageClassCompatibility`, where `abelianComparisonFree` is defined.
No original module is pruned. New support
modules expose only the imports required by their definitions or statements;
proof-only coherence imports remain private.

## Where the brief, the DAG or earlier work was wrong

The supplied node tree has no node attached to this item, despite the declaration's
blueprint marker `lem-sc-raw-derived-class-affine-descent`. Added that node with
the unchanged statement and the proof actually implemented. Some already proved
support APIs (`RawRestrictedDerivedComparison`, its pullback theorem, and
`FixedDerivedCohomologyDiagram`) likewise have no attached nodes in this snapshot;
the report and new proof steps name the exact APIs used instead of replacing them
with new holes.

A direct unfolding of the raw and chart pullback definitions repeatedly compared
two free-sheaf presentations. Profiling isolated kernel conversion as the cost;
the canonical abbreviation repair preserves definitional equality and the target
statements. The composition square must use derived inverse-image associativity,
not just functoriality of cohomology: the new naturality module proves this square,
including its shifts and bounded-below inclusion comparison.

The required LeanSearch request returned an internal server error and is recorded
as unavailable, without a mathematical verdict. LeanFinder, Loogle and Mathlib
source searches completed; their useful generic results are used in the proofs.

## New nodes

`lem-sc-raw-derived-class-affine-descent` records the unchanged item theorem and
its affine-model, limit-cone, continuity, evaluation, and transport proof.

`def-sc-raw-fixed-derived-comparison` records the explicit canonical comparison
from raw Hom with fixed-base coefficients to hypercohomology of the pullback chart.

`lem-sc-raw-fixed-derived-comparison-is-iso` records invertibility of this
comparison, proved from existing raw derived evaluation and functoriality.

`lem-sc-raw-fixed-derived-comparison-naturality` records the fully proved
pullback square. No new node has an unproved Lean theorem.

## Second reading by A2

1. **Statements and signatures — PASS.** I diffed the delivered item against the repository version. The existing theorem signature is unchanged byte for byte; the added comparison declarations match their DAG node statements. The raw pullback abbreviation change is recorded in `coord/changes/raw-derived-pullback-canonical-free.md` and is definitionally equal to the old free-sheaf expression.
2. **Proof and axioms — PASS.** I compiled all delivered modules with `lcompile.py --all`, searched for forbidden declarations and unsanctioned `sorry`, and checked the five public declarations with `#print axioms`. They compile without warnings and use only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Split statements and prior declarations — PASS.** The three added declarations are explicit construction, invertibility, and pullback naturality lemmas; each is strictly supporting the descent proof and is not a restatement of the item. Repository and Mathlib searches found no duplicate declaration. No new sorry or hollow definition remains.
4. **Shortest route and pruning — PASS.** The proof uses the existing affine-model, fixed-coefficient continuity, raw evaluation, and inverse-image coherence APIs, then constructs only the necessary pullback cone and transport identity. The original item imports are retained where used; the new comparison module’s free-sheaf import was narrowed to the defining module. No original item dependency was pruned.
5. **DAG and unit route — PASS.** The four node records agree with the declarations and proof steps after correcting the isomorphism node’s mismatched citation. The unit’s `realized` fields are empty in the supplied snapshot; the delivery leaves the unit route unchanged and follows its parent node’s affine-model and continuity reduction. The tool use for the continuity theorem is recorded on the item node.

Second reading moved the new isomorphism theorem unchanged into its own `RawFixedDerivedComparisonIsIso` module and updated its node, as required for a new statement. It also narrowed the new comparison module’s free-sheaf import from `AbelianFreeRepresentablePullback` to `AbelianHigherDirectImageClassCompatibility` and restored the item signature’s original spacing. `UpperLowerStarCoherence` stays public because `upperStarCompDerivedPlus` occurs in the naturality statement. I also removed an incorrect DAG edge from the fixed-comparison isomorphism node: the proof uses the generic proved `isIso_rawRestrictedDerivedComparison`, whereas the cited old node states only the specialized F[0][p] evaluation theorem. Its proof text now names the exact generic API, which has no attached node in this snapshot. No mathematical statement or proof body changed. The temporary axioms scratch file was removed before delivery.

Change record: `coord/changes/raw-derived-pullback-canonical-free.md`.
