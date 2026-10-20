## What changed

Proved `SheafOfModules.ringedProjectionFormula_totalization_right` with its exact
original statement. The specified second component is the localization of an
ordinary chain isomorphism conjugated by the canonical representatives, hence is
itself an isomorphism. The existing first inverse equation identifies the first
component with its inverse. `CategoryTheory.comp_hom_eq_id` and
`CategoryTheory.IsIso.hom_inv_id` finish the second inverse equation.

Added the proof-only import
`Sheaf.Paper.ringedProjectionFormula_totalization_left`. Updated the item's DAG
proof and proof dependencies to this shorter argument. The two existing public
imports, all declaration signatures and definitions are unchanged.

Validation: the final proof with pruned imports compiled via `lcompile.py` in
7.3 seconds, with no errors or warnings. The import-direction check confirms that
the new proof import is acyclic. The generic inverse-uniqueness argument includes
zero objects, rank-zero coefficients and all bounded supports without case splits.
LeanFinder found the exact generic inverse-uniqueness lemma; Loogle returned no
match for the attempted query; the scripted grep service timed out and was recorded
as unavailable. Repository searches located the already defined total-chain inverse
and the existing left-conjunct theorem.

## Proved and sorry left

Closed 1 existing hole:
`SheafOfModules.ringedProjectionFormula_totalization_right`
(node `new-lem-weil-pbc-projection-formula-totalization-right`).

No holes remain in the item; no holes or declarations were added elsewhere;
0 statements were split off. This is a proof from existing named declarations,
including `SheafOfModules.ringedProjectionFormula_totalization_left` and
`CategoryTheory.tensorAdjunctionTotal_isIso`, whose existing unfinished proofs
remain in their own modules. The first-conjunct module was already imported by
`Sheaf.Paper.ProjectionFormulaTotalization`, so this introduces no new hole into
that parent's import closure.

## No longer needed

Removed these 19 unused direct proof imports:

- `Sheaf.Paper.StrictPerfectCoefficientPackage`
- `WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Paper.ProjectionFormulaProjectiveSummand`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`

Their APIs are either already available through the retained statement import or
are unnecessary for this proof. In particular the derived projective-summand and
pro-etale specializations are unnecessary as direct dependencies of the second
conjunct. The signed finite-total argument itself stays in the existing arrow
construction, and the representative/derived-adjunction identification stays in
the left-conjunct theorem. Neither unit statements nor their realized steps are
bypassed. The original sole declared dependency,
`def-weil-pbc-projection-formula-arrows`, remains needed. No existing declared
proof dependency was dropped and no whole module is claimed globally unreachable:
the first-conjunct module and other consumers can still import the removed modules.

## Where the brief, the DAG or earlier work was wrong

The original node planned to expand and normalize the canonical representatives
again for the second equation. That repeats work already assigned to the first
inverse equation. Since the second arrow is already built from a chain inverse,
its invertibility plus the first equation suffices. No statement or definition
repair was necessary, and no new result was handed on.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
