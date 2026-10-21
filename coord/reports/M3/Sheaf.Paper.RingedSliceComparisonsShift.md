## What changed

Filled `SheafOfModules.ringedSliceComparisonsShift` without changing any existing
signature, definition, public import, or docstring. The proof applies the existing
normalized derived-square and adjunction-mate declarations, then applies the existing
slice tensor shift theorem twice. Proved private helpers translate between its
natural shift comparisons and the item's pointwise normalization; equality on
sheafified pure tensors fixes the signs. The normalized-unit proof from
`DerivedAdjunctionShift` is instantiated directly on complexes via private helpers,
so no homotopy-presentation assumptions are added. Updated the existing node's proof
text and proof dependencies to describe this assembly. No source-library files changed. The proof namespace/section commands are documented
in `coord/changes/M3-ringed-slice-comparisons-shift-proof-scopes.md`.

## Proved and sorry left

Closed the one existing hole:
`SheafOfModules.ringedSliceComparisonsShift`
(`lem-weil-pbc-ringed-slice-comparisons-shift`).

Item holes: 1 before, 0 after. Holes added: 0. Split off: 0.
Validation: the complete item compiled through `lcompile.py` (30.9 seconds after replacing the concrete normalization simplification by direct
application of the generic cancellation lemma).
All five existing public signatures and all public imports are unchanged.
Every private helper is proved. Existing unfinished declarations imported from the
DAG remain dependencies; this delivery adds no unfinished declaration.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`:
  publicly exposed by the required pushforward-composition module.

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the tensor dependency
  performs the resolution/descent argument.
- `Sheaf.Paper.RingedSliceDerivedComparisons`: the supplied `_normalized` equation
  already supplies its required normalization. Removed that direct proof edge from
  the item node.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: exposed by the required
  generic derived-square module.
- `Mathlib.CategoryTheory.Shift.Adjunction`: already exposed by the retained public
  import of `DerivedAdjunctionShift`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`: the
  slice tensor dependency performs this descent internally.

No complete module is withdrawn or claimed to leave the targets' closure. In
particular, the source declarations and the unit route remain intact.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The advertised short assembly needs two Lean
interface translations: the derived-adjunction shift declaration is on homotopy
presentations whereas the item's data are on complexes, and the slice tensor theorem
uses natural chain shift families whereas the item's normalization quantifies over
pointwise chain isomorphisms. The proved private Kan-extension and tensor-generator
helpers supply these translations without weakening the hypotheses or conclusion.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
