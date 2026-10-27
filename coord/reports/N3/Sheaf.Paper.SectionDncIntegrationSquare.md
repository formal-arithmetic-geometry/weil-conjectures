## What changed

Reduced both theorem clauses of Sheaf.Paper.SectionDncIntegrationSquare to their
normal-bundle factors, preserving every existing declaration signature and the
unit's DNC/vector-integration route. The base-change proof takes the normalized-base
component of SectionRestriction.coherence, composes it with the normal-integration
square, and uses associativity and Functor.mapIso_trans. The diagonal proof
identifies the normal factor with chartDiagonalBeta and invokes the existing
diagonalDncAssemblyGlobal, using DNC uniqueness for the two chosen comparisons and finishing by associativity.

Moved normalIntegration, with identical signature and complete construction, into
Sheaf.Paper.NormalSectionIntegrationData. The original module publicly reexports
it. This permits the two normal-factor statements to precede the composition
without an import cycle. All existing public imports of the item are retained.
The original node's Lean ownership and proof route follow this arrangement.

Added two strictly smaller statements, each in a separate module, with complete
proof plans, sources and DAG nodes. They neither contain psi nor repackage the
original theorem's hypotheses. In particular neither states the DNC-specialization
square or the diagonal alpha/delta/beta assembly. Their edge cases include arbitrary
non-flat base change, rank zero and empty schemes. The Tate transport argument in
the orientation statement is normalized, not an arbitrary orientation.

## Proved and sorry left

Closed the two original bodies with complete Lean proofs from named statements:

- WeilConjectures.PurityFiniteSetting.SectionIntegration.section_dnc_integration_baseChange.
- WeilConjectures.PurityFiniteSetting.SectionIntegration.section_dnc_integration_diagonal.

The item itself has zero sorry. Two holes are added, so this is a decomposition
(two holes closed, two added), with zero net hole reduction:

- WeilConjectures.PurityFiniteSetting.SectionIntegration.normalIntegration_baseChange,
  in Sheaf.Paper.NormalSectionIntegrationBaseChange;
  node lem-pur-normal-section-integration-base-change.
- WeilConjectures.PurityFiniteSetting.SectionIntegration.normalIntegration_eq_sectionOrientation,
  in Sheaf.Paper.NormalSectionIntegrationOrientation;
  node lem-pur-normal-section-integration-orientation.

The relocated definition has zero holes. Existing imported theorem holes remain
with their existing owners, including diagonalDncAssemblyGlobal. This delivery
claims no axiom-free proof of the targets.

## No longer needed

Removed the item's proof-only imports Sheaf.Paper.VectorIntegrationSiteComparison,
Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange and
Mathlib.CategoryTheory.Adjunction.Mates. Their geometric and mate-comparison work
is retained in the normal-square lemma's proof plan, not bypassed.

The parent proof no longer directly invokes def-pur-conventions,
lem-pur-dnc-section-geometry, thm-pur-dnc-invariance,
def-pur-finite-section-comparison, def-pur-co-smoothness,
lem-pur-vector-integration-site-comparison, thm-cbc-finite-level-proetale,
lem-weil-pbc-mate-pasting, cor-pur-vector-bundle-purity,
lem-pur-diagonal-base-change or det-sp-orientation-charts. These are either still
statement prerequisites or retained below the normal-square/coherence/assembly
interfaces. They are not globally pruned. The parent's obsolete direct tool_uses
entry lem-weil-pbc-mate-pasting is withdrawn; the new normal-square node explains
its generic mate-calculus use. No module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false, and no target was changed. The original
plan's two independent squares are sufficient for the first clause; duplicating
DNC naturality or redoing the integration-site comparison in the composition is
unnecessary. The diagonal clause requires identification of the two normal-factor
presentations, which is not definitionally the same construction: the original
uses the conormal model and bundleSectionAdjoint, while chartDiagonalBeta uses the
normalized ordinary section orientation. That coefficient/compositor comparison
is isolated explicitly rather than assumed by a change tactic.

The existing normalModelSectionOrientation is close but takes a specified bundle
presentation and an adjunct gamma; it does not itself identify the zero-section
coefficient compositor with bundleSectionAdjoint. The new orientation lemma asks
only for this conormal specialization and coefficient comparison, followed by
comparison-site functoriality. Its proof plan records the existing lemma as the
main step.

The global diagonal assembly and normal-model orientation nodes belong to
sk-thm-smooth-purity, which sk-prop-sp-purity-bc directly cites. They also follow
the original item's chart-normalization source. Their use preserves the actual normal bundle, specified DNC map
and integration normalization. It does not replace the unit's argument by another
purity theorem. The independent reader should confirm this route specialization;
no maintainer tool-use approval is added here.

## New nodes

`def-pur-normal-section-integration-data` owns the relocated actual construction,
with the same projection and augmentation equations and no missing data. Its
module is Sheaf.Paper.NormalSectionIntegrationData.

`lem-pur-normal-section-integration-base-change` isolates original proof Steps 1,
3 and 4: conormal-model base change, inverse integration-adjunct naturality and
etale/pro-etale mate compatibility. Its module is
Sheaf.Paper.NormalSectionIntegrationBaseChange. The source is base-change factors
Proof (1).

`lem-pur-normal-section-integration-orientation` isolates the normal factor in
original Step 6, using normalModelSectionOrientation and the coefficient pullback
compositor. Its module is Sheaf.Paper.NormalSectionIntegrationOrientation. Sources
are orientation chart Step 4 and the diagonal clause of base-change factors (1).

Change record: coord/changes/normal-section-integration-relocation.md.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
