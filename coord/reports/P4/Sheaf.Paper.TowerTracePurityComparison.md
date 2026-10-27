## What changed

Replaced the assigned theorem's sorry by a complete assembly proof from four strictly
smaller bridge statements. All definitions were extracted, with unchanged names,
signatures and bodies, into the publicly reexported TowerTracePurityComparisonData.
This is needed to let each remaining bridge live in its own acyclic module. The
change record is coord/changes/tower-trace-comparison-data-extraction.md.

The private proved helper insert_composite inserts a factorization into a fixed
composition word using associativity, keeping the geometric maps folded during
elaboration. The assembly applies the actual adjunction Hom equivalence to the inverse adjunct
formula, takes underlying arrows, and cancels tensorSource.hom with tensorSource.inv.
It compares any permitted base orientation using only rank-one reduction injectivity,
substitutes the scalar counit equation, and proves integral tracePurity equals tower.
It identifies the canonical integral representative, explicitly localizes the
composition, and unfolds rationalIso with its prescribed source/exceptional/representative
comparisons. Finally it reverses rationalIso_scalar and maps that equation through
commonImage. No new lemma contains the rational or common-stage conclusion.

Remote lcompile validated the data module and all four bridge statement modules.
The complete assembly compiled in 40.6 seconds. Its dependent coefficient/source
conversions require a declaration-local maxHeartbeats 300000 allowance, explained
by a comment; the required 60-second compile limit is unchanged. The delivery tool
performs the final clean compilation and preflight checks.

The four bridge docstrings contain the source places and complete arguments. Their
statements were checked against empty schemes, d=0, zero input, disconnected X,
E=the base field and F=E. Rank-one uniqueness allows noninvertible arrows and makes
no claim of faithfulness of finite evaluations on arbitrary derived morphisms.
CoefficientComparison fixes compact support and coefficient-unit normalization,
and IsJNormalized/IsUnitNormalized fix the tensor and unit coordinates; the bridges
do not allow arbitrary endpoint isomorphisms. The unit's realized route is unchanged.

## Proved and sorry left

Closed the original hole:
WeilConjectures.TowerTracePurityComparison.tower_trace_purity_comparison
(lem-pur-tower-trace-purity-comparison).

Added four holes, exactly one public theorem in each new module:

- WeilConjectures.TowerTracePurityComparison.normalized_presentations
  (lem-pur-tower-trace-normalized-presentations): simultaneous normalized presentations,
  their invertible prescribed unit orientations and raw inverse-adjunction formula.
- WeilConjectures.TowerTracePurityComparison.prescribed_orientations_unique
  (lem-pur-tower-trace-orientation-uniqueness): rank-one injectivity in the published Stage
  coordinates, with no scalar or rational assertion.
- WeilConjectures.TowerTracePurityComparison.scalar_counit
  (lem-pur-tower-trace-scalar-counit): ordinary coefficient extension of the unit counit
  trace, with no general-input purity assertion.
- WeilConjectures.TowerTracePurityComparison.canonical_integral_transpose
  (lem-pur-tower-trace-canonical-integral): comparison of ordinary canonical integralMap
  and the completed trace transpose, before localization.

This is a decomposition: one original hole closed and four smaller holes added
(raw declaration count -3, before any import-closure pruning).
There are zero holes in the assigned module and zero in the extracted data module.
Each remaining proof is exactly `by sorry`, not a partial anonymous proof or definition.

## No longer needed

Removed the direct private import Sheaf.Paper.AdicPurityScalarNaturality. Its theorem
lem-pur-adic-purity-scalar-naturality is not used by this assembly: rationalIso is
compared via its actual canonical integralMap construction. Its unused entry in the parent node’s top-level tool_uses list was removed, preserving
the order of all other approvals. Its interface data remain
publicly available through the unchanged imports; this does not withdraw or remove
any declaration or claim it is unused elsewhere.

Removed the direct private imports TowerPurityRealizedTranspose and
IntegralOrientationReductionInjectivity. Their declarations remain the proof tools
recorded in the smaller bridge nodes; those holed statements import only their
statement data until their proofs use these tools. Their nodes remain needed. Every original public import is preserved through
the public data-module import. No source-library declaration or module is removed.
No mathematical route is bypassed and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical route is sound. The existing declarations expose different
normalized presentations: realized_tower_purity_transpose existentially chooses a
realization and ring system, while this item fixes S and uses R.model. Thus simply
applying that theorem does not supply Stage for those models. Similarly,
reduction_injectivity is stated in whole-tower rho coordinates, not this item's
scalarReductionDerivedExtension/finiteReduction coordinates. The extracted lemmas
state these genuine normalization bridges rather than duplicate the underlying theorems.

The final rational comparison also needs comparison of ordinary and completed
projection words; the new canonical_integral_transpose isolates that integral step.
The existing rationalIso_scalar already gives the entire required scalar equation;
no new rational scalar assertion is needed. The parent DAG now describes the actual
Lean assembly. Data extraction preserves Comparison verbatim.

## New nodes

The definition node def-pur-tower-trace-comparison-data owns the moved existing
presentation declarations; it introduces no duplicate construction or additional
choice. Four statement nodes correspond to the four holes listed above, each
strictly smaller than the original integral-plus-rational comparison. Their source
places are tower-gamma clauses (1)--(2), field-extension-towers clause (2), and
purity-transport Steps 1--2 in literature/blueprint/latest. Searches used LeanSearch,
Loogle, LeanFinder and Mathlib grep; the generic adjunction identities were useful,
but none states these normalized geometric comparisons. A whole-blueprint search
for "trace transpose" found no additional node. Existing Sheaf and adopted source
searches found the abstract interfaces described above, which the bridge proofs use.

The canonical integral bridge uses completed projection coherence and adic
projection/shift coherence as generic tools; their applicability is the same
finite-Tor and normalized-augmentation setting as the existing constructions.
No tool_uses approval field was added by this worker.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
