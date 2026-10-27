## What changed

Factored the unchanged affine diagonal coordinate and integration constructions into
`Sheaf.Paper.AffineDiagonalIntegrationConstructions`, publicly reexported by the original
module. This avoids an import cycle between the two new mathematical obligations and
their consumer. Existing public signatures and non-theorem bodies are identical.

Reduced `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegrationOrientation` to
`affineDiagonalTraceRestriction` (trace, invertibility and diagonal restriction) and
`affineDiagonalDncNormalization` (normalized DNC comparison in difference coordinates).
The item supplies the complete assembly: rewrite delta followed by beta using the DNC
equation, then invert the isomorphism equality T followed by alpha equals comparison(I).
The private `inverse_composite` proof uses `Iso.ext` and `congrArg Iso.inv`;
`orientation_composite` combines this with the DNC equation.
The trace lemma has no DNC arrow; the DNC lemma has no I on X→Y or alpha comparison.
Neither is the original conjunction with renamed hypotheses.

Change record: `coord/changes/P2-affine-diagonal-integration-step-modules.md`.
All single-file validation runs through lcompile.py, in sandbox import order.

## Proved and sorry left

Decomposition: the body of `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegrationOrientation`
is complete, from two strictly smaller public statements. One upper hole is removed and two
lower holes are added; this is a decomposition, not a sorry-free proof of model agreement.

New holes, each with a full natural-language proof and its own module/node:

- `WeilConjectures.PurityFiniteSetting.affineDiagonalTraceRestriction`
  (`lem-pur-affine-diagonal-trace-restriction`).
- `WeilConjectures.PurityFiniteSetting.affineDiagonalDncNormalization`
  (`lem-pur-affine-diagonal-dnc-normalization`).

Untouched holes in the original module, all on
`lem-pur-affine-diagonal-integration-orientation`:

- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_translation`.
- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_exponent`.
- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_zero`.

The construction module has zero holes. The normal-coordinate proof from the initial
source snapshot is retained: it uses `affineDiagonalGradedCoordinates_isIso` and the
normalized projection equation, rather than assuming the coordinate isomorphism.
Five holes remain in the complete delivery, three old and two new.

## No longer needed

Removed the original proof-only imports from the item; all proof-relevant geometry
now resides in its construction dependency. The construction module retains only
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
`Sheaf.Paper.AffineDiagonalGradedCoordinates` as direct proof imports. Its public
prerequisites, and all original public prerequisites of the item, stay unchanged.

The following former proof-only imports are absent as direct imports of both item
and construction modules:

- `Sheaf.Paper.ProjectionFormulaCoefficientCoherence`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`.
- `Sheaf.Paper.TraceTransposeBaseChange`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.PurityDncComparisons`.
- `Sheaf.Paper.AffineTranslationTrace`.
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`.

The parent node's former tool approvals are removed from its direct proof route:
`lem-weil-finite-compact-projection-formula`,
`lem-weil-pbc-finite-type-over-noetherian`, `sbc-lem-affine-space-smooth`,
`lem-weil-pbc-proetale-derived-pullback-composition`, `lem-pur-dnc-section-geometry`,
and `thm-cbc-finite-level-proetale`. Their uses are recorded in the appropriate
new step nodes for independent review.

Their mathematical obligations remain in the proof plans of the smaller statements
or in the three untouched ancillary clauses. This delivery claims no global pruning
of those nodes or modules. No blueprint unit or parent route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing declarations provide the mathematical ingredients but not their
coherence in the concrete presented-transpose coordinates. In particular, the
pro-etale trace-transpose theorem is not directly the ordinary-etale comparison
formula used here, and the DNC normalization still needs transport through the
explicit translated product and normalized Rees coordinates. The two new statements
isolate these gaps without adding hypotheses, changing coefficient levels, choosing
an arbitrary orientation, or weakening the conclusion.

Edge checks: both statements retain d=0 and empty Y. They quantify over every
normalized Rees comparison. The DNC lemma requires that J and Q are exactly the
actual presented transposes; it makes no assertion for arbitrarily oriented maps.
The construction move addresses an import cycle, not a compile timeout.

## New nodes

- `def-pur-affine-diagonal-integration-constructions`: records the existing real
  constructions relocated to a dependency module, with no new mathematical choice.
- `lem-pur-affine-diagonal-trace-restriction`: the original plan's trace and diagonal
  steps 1–4, including invertibility of the three actual transposes.
- `lem-pur-affine-diagonal-dnc-normalization`: the original plan's ordered-coordinate,
  translation and standard-pair normalization steps 5–7.

Each inherits the original smooth-purity unit and source. LeanSearch, LeanFinder,
Loogle and source searches found no theorem giving either complete comparison
formula. The parent node now records the actual Lean assembly and retains the
original plans for its three unfinished ancillary statements.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
