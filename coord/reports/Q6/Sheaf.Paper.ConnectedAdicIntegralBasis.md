## What changed

Proved `WeilConjectures.connected_adic_integral_basis` with its original signature and
public scalar-map abbreviation unchanged. All added helpers are private and proved.
The DAG proof and declaration docstring now describe the implemented argument.

The proof constructs the constant-to-continuous-function comparison at the independent
coefficient and scheme universes required here, then identifies connected sections with
constant values. Rank-one adic completeness reconstructs the completed ring sections
from their residues. Projection formulas identify the actual coefficient inclusion.
Finally, it constructs the prescribed-basis morphism explicitly and proves it invertible
using the existing finite-free comparison and detection by global sections on finite
free sheaves. The categorical argument also covers rank zero; nonempty connectedness
is used only for recovering the unique constant value.

Validation: the complete module compiled cleanly through `lcompile.py`; the public
theorem signature was compared with the repository source and is unchanged. No other
module, statement, definition, or public import was changed.

## Proved and sorry left

Closed the sole original hole: `WeilConjectures.connected_adic_integral_basis`.
Proved 1 of 1 original sorries; added 0 holes; split off 0 statements; 0 sorries remain
in the delivered module. Existing imported theorems are used as stated.

## No longer needed

Removed these direct proof imports and corresponding direct proof dependencies:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
  (`lem-weil-l-adic-extension-integers-dvr`): no direct DVR factorization is needed;
  the completed comparison already specifies the actual coefficient map by projections.
- `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`
  (`lem-pur-proetale-finite-constant-sections`): its coefficient universe does not fit
  this statement. A private proved continuous-function comparison handles arbitrary
  coefficient universes and does not require finite quotients.
- `Sheaf.CategoryTheory.AdicBasisLimit` (`lem-pur-adic-basis-limit`): use the existing
  finite-free completed scalar comparison and change to the prescribed basis through
  global sections, rather than specializing the general adic-basis theorem again.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`: no local compactness or quotient
  finiteness is used in the direct argument.

The direct dependency `lem-weil-valued-dvr-finite-quotients` is also unnecessary:
continuous maps to any discrete ring suffice. The exploratory import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` was removed; the proof uses finite
biproducts and the unit hom/section equivalence directly.

These are removals from this proof's direct dependency list, not module withdrawals.
The existing completeness and finite-free comparison may still use some of these
results transitively. The existing approved DVR tool-use record is preserved.
No library module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing finite constant-section theorem is tied to coefficient universe `t + 1`,
while this item's statement has coefficients in `max u (t + 1)` with independent `u`
and `t`. It cannot be applied directly at the required universes. The private proved
comparison supplies this missing generality without changing any public interface.
The original proof plan also repeats an adic-basis specialization already supplied by
`finiteFreeCompletedScalarComparison`; the finite-free/global-section argument avoids
that duplication while retaining the prescribed sectionwise formula.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
