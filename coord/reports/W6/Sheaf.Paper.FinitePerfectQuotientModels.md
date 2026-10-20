## What changed

Withdraw lean/Sheaf/Paper/FinitePerfectQuotientModels.lean under brief step 8d:
the current library has no importer or external declaration user. Set the Lean
attachment of lem-weil-pbc-residue-perfect-finite-quotient-models to null, preserving
the mathematical node, its statement and its proof plan. The item does not realize
a unit statement or proof step. No consumer requires adaptation.

The original module and two new private covering/restriction lemmas were compiled
successfully earlier in this session. Those unused helpers are not delivered.
An independent source import-graph traversal confirms the item is outside both
TargetsCheck and Challenge; there are no missing Sheaf or WeilConjectures import
sources. The delivery dry run additionally checks that no module imports the
withdrawn file.

Change record: coord/changes/W6-withdraw-unused-finite-perfect-quotient-models.md.

## Proved and sorry left

Original holes: 1, in AlgebraicGeometry.Scheme.residuePerfect_quotient_models_succ
(node lem-weil-pbc-residue-perfect-finite-quotient-models).
Holes proved: 0. Holes added or split off: 0. Holes left in delivered Lean: 0.
The original hole is removed by withdrawal of the unused module, not counted as a
proof or decomposition. No retained theorem is weakened and no new theorem replaces it.

## No longer needed

Pruned module: Sheaf.Paper.FinitePerfectQuotientModels, including
residuePerfect_quotient_models_succ, residuePerfect_finite_quotient_models,
FinitePerfectModelsOn, HasUniformFinitePerfectModels, and the coefficient and
restriction helpers defined only there.

All imports of that withdrawn module disappear with it:

- Sheaf.Paper.CompletedAdicIntrinsicCompletion
- Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
- Mathlib.Algebra.Category.ModuleCat.Ulift
- Mathlib.AlgebraicGeometry.Sites.Etale
- Mathlib.AlgebraicGeometry.Noetherian
- Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
- Mathlib.CategoryTheory.Abelian.ShortExact
- Mathlib.CategoryTheory.Sites.Pullback
- Mathlib.CategoryTheory.Sites.Abelian
- Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
- Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
- Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
- Sheaf.Paper.NilpotentReductionLissity
- Sheaf.SixFunctors.ConnectedEtalePerfectConstant
- Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

These dependencies may remain needed elsewhere; this delivery makes no claim that
they can themselves be withdrawn. No additional module or DAG node is deleted.
The mathematical node remains available for any future route that needs it.

## Where the brief, the DAG or earlier work was wrong

The dispatch described this module as reached by the targets. On the current shared
source tree it has no importers or external declaration references. In particular,
its former consumers Sheaf.Paper.ResidueLissePerfectLift and
Sheaf.Paper.FinitePerfectAdicRealization no longer have source files. The import
closures of TargetsCheck (9537 modules) and Challenge (2777 modules), counting
external imports, both exclude the item. This is why step 8d applies.

The mathematical claim is not disputed. Its existing DAG proof plan is preserved;
only the stale Lean attachment is removed. No new node is introduced.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
