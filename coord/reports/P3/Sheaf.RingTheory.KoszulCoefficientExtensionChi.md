## What changed

Withdrew `lean/Sheaf/RingTheory/KoszulCoefficientExtensionChi.lean` using
`deleted.txt`. Its sole public theorem duplicated the stronger proved upstream
`ExteriorAlgebra.exists_koszul_coefficient_extension_chi` in
`WeilConjectures.RingTheory.KoszulCoefficientExtensionChi`.
Reattached `new-lem-sc-koszul-coefficient-extension-chi` to that upstream theorem;
the node statement, proof and proof dependencies remain unchanged.
Change record: `coord/changes/retire-koszul-coefficient-extension-chi.md`.

The original file compiled in 4.9 seconds. A separate sandbox example with its
original signature and the direct proof
`exact ExteriorAlgebra.exists_koszul_coefficient_extension_chi A r f S`
also compiled. The upstream theorem's printed axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`. No source-library files are changed.

## Proved and sorry left

Zero holes on entry; zero holes remain. Holes closed: none. Holes added: none.
Split-off statements: none. This is removal of an unused duplicate, not a proof
or a decomposition. The unchanged upstream theorem proves the original
existence and evaluation formula without the extra hypotheses.

## No longer needed

Pruned module: `Sheaf.RingTheory.KoszulCoefficientExtensionChi` and its duplicate
public declaration and private constructions. A full-library text search and
`tools/downstream.py` found no importers of this module. Its former parent,
`WeilConjectures.RingTheory.KoszulCoefficientExtension`, already imports and
uses the upstream Chi theorem. No consumer adaptation is needed.

The withdrawn file's imports disappear:
- `WeilConjectures.RingTheory.KoszulDualComplex`
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `Mathlib.LinearAlgebra.ExteriorPower.Basic`
- `WeilConjectures.RingTheory.KoszulRegularSequence`
- `Mathlib.RingTheory.Localization.Defs`
- `Mathlib.LinearAlgebra.ExteriorPower.Basis`

These dependencies remain needed by the upstream implementation; no dependency
node or source-library declaration is claimed to be globally pruned. The existing
node is preserved and redirected. Its unit's `realized` arrays are empty, and the
upstream proof retains exactly the exterior-basis construction and differential
argument, so no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The dispatched module has no remaining `sorry` and compiles unchanged. The DAG
attachment still pointed to its weaker Sheaf duplicate although the upstream
library already proves the formula for arbitrary algebras and its parent already
uses that stronger declaration. The old twin-retirement list had retained the
Sheaf file because of the signature difference; the old statement is now
compiler-checked as an immediate specialization of the upstream statement.
The node's mathematical statement is unchanged, including its original
regularity and localization hypotheses. No false statement was found.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
