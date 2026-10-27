## What changed

Proved `WeilConjectures.CompactSupportRealizationFactorization.coefficientFactorization`
in `Sheaf.Paper.CompactSupportRealizationFactorization`. Both the finite-extension and
finite-extension-valued algebraic-closure clauses follow by expanding `condensedProjection`
and `pasteScalar`, then removing the identity components of the functor associators.
The proof uses definitions and category identity laws; it does not apply another holed
factorization theorem. No declaration signature, definition, public import or docstring changed.

## Proved and sorry left

Closed one of the six existing holes: `coefficientFactorization`. Added zero holes and
split off zero statements. The following five holes remain unchanged, all in namespace
`WeilConjectures.CompactSupportRealizationFactorization` and attached to
`lem-pur-compact-support-realization-factorization`:

- `compactSupport_realization_factorization`
- `identityProperReduction`
- `identityProperRealization`
- `identityProperCoefficient`
- `q_naturality`

This is a partial delivery with one direct proof, not a decomposition. The main existence
and normalization theorem is still open. The final module compiled with `lcompile.py`
(exit code 0, 46.2 seconds), including the import removals.

## No longer needed

Removed these eight private proof imports, unused by the definitions, statements and the
completed coefficient-factorization proof:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.CompletedCoefficientPushforwardComparison`
- `Sheaf.Paper.CompactSupportReductionTower`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.Paper.CompletedDirectImageLimits`

No DAG node or library module is withdrawn. These mathematical inputs remain in the plan
of the five untouched holes, and some are also imported transitively. No claim is made
that they have left the targets' closure. The original node's Step 7 already describes the
proved definition-expansion argument, so its proof plan and dependency fields stay unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The original Step 7 applies equally to finite coefficients and
the finite-extension-valued Omega coefficient ring: the same proper/open pasting definition
works for both. A bare `rfl` does not suffice because the definition includes functor
associators; their identity components must be simplified explicitly.

The open-mate theorems found during the search (`integralOpenMateNormalization` and
`openReconstructionEffectivity`) have geometric or Tor hypotheses absent from the remaining
unrestricted naturality statement. They were not applied by silently strengthening that
statement. The remaining identity-proper equations also require compatibility with the
specified section-normalized identity unitors, not merely existence of some identity iso.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
