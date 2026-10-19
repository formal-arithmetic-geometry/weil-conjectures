## What changed

Completed `punctured_curve_has_dvr_branches` without changing its statement, its
existing docstrings, or any public definition. Four private proved helpers establish
the dimension of each minimal-prime quotient, henselian locality of a finite domain
algebra, the normalization properties, and the canonical total-fraction-ring
comparison. The final proof identifies the principal puncture with the finite
coproduct and checks the equation over Spec R on every coprojection.

Updated the node's proof, proof dependencies and proof origin to describe this Lean
argument. Its eight-step normalization and principal-localization route is preserved.
No new modules or statements with holes were introduced.

## Proved and sorry left

Closed the one original hole: `punctured_curve_has_dvr_branches`
(node `lem-exc-punctured-curve-branches`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the delivered module, and there are no split statements.
The proof uses the existing declared normalization, Nagata, excellence,
principal-parameter and total-fraction results; this delivery does not claim to
close their transitive dependencies.

## No longer needed

Removed these direct proof imports:

- `Mathlib.RingTheory.LocalRing.Quotient`: no quotient-module lemma is needed;
  locality is proved directly from the surjective quotient map.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: publicly re-exported by
  `Sheaf.RingTheory.ReducedNoetherianTotalRingFractions`.

- `WeilConjectures.AlgebraicGeometry.Regular`: the proof uses Mathlib's
  `IsDiscreteValuationRing.TFAE` directly instead of passing through regularity.
- `Sheaf.RingTheory.FiniteOverHenselianLocalProduct`: retired compatibility module;
  the proof imports its upstream replacement directly.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`: already publicly available
  through `Sheaf.AlgebraicGeometry.LocalCurveBranches`.
- `Sheaf.RingTheory.NagataRing` and `Sheaf.RingTheory.JapaneseDomain`: already
  publicly available through `Sheaf.RingTheory.QuasiExcellentNagata`.
- `Mathlib.RingTheory.Finiteness.Defs` and `Mathlib.RingTheory.FiniteType`: already
  available through the retained Nagata and excellence inputs.
- `Mathlib.Algebra.Algebra.Pi` and
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: already publicly available
  through `WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: already publicly available
  through `Sheaf.RingTheory.IsExcellentFiniteTypeLocalization`.

Removed `lem-sc-normal-dim1-dvr` from the item's proof dependencies and top-level
`tool_uses`: Mathlib's DVR criterion supplies this step. Removed the direct proof
dependency `def-weil-pbc-module-localization`: the comparison uses the existing
localization and fraction-field algebra equivalences, rather than an additional
argument with the module-localization equality criterion. The definition remains
available transitively where the retained dependencies need it.
All other declared dependencies are retained. These are removals from this item's
route; no claim is made that the modules are unreachable from every other target.

## Where the brief, the DAG or earlier work was wrong

The `lem-sc-normal-dim1-dvr` node is attached to regular-local-ring declarations,
whereas the required DVR conclusion follows directly from Mathlib's
`IsDiscreteValuationRing.TFAE`. No attachment, statement or definition repair is
needed for the present proof. A quotient-local-ring instance needed an explicit
construction using the surjective quotient map. The residue characteristic
assumptions are retained in the theorem, although its proof works in every
characteristic. There is no unit-route departure.

The initial continuation dry run could not reach the compile server after its
retries; this was a service failure, with no Lean diagnostic.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
