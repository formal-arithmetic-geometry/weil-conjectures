# AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology

## Reason

Restore the quarantined stage-3 rework item with its complete original proof and statement.
The archived public restriction module has since been withdrawn. Compiling the archive
reports unknown identifiers `Scheme`, `Quiver.Hom`, and `QuasiCompact`, because its statement
no longer receives its public prerequisites. Its private imports also include retired
Sheaf helpers. Select the actual current statement providers and retain only the two
proof imports used by the existing colimit argument.

This preserves the small coordinate-ring-colimit strict-henselization scheme and its
structural map. The adopted source theorem uses the canonical `strictLocalization` model;
substituting that theorem directly would change the assigned statement. No source-library
file, target statement, definition body, or quarantine archive is changed.

## Old

Archived header:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
import Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

The theorem signature and entire text from the module docstring onward are preserved
byte for byte. In particular the theorem uses `Scheme.strictHenselizationScheme s` and
`Scheme.strictHenselizationStructuralMap s`, with qcqs f, every geometric point s,
every bounded-below K and every integer n.

## New

```lean
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
```

`Mathlib.CategoryTheory.Sites.GlobalSections` supplies `Sheaf.Γ`.
`StrictHenselizationStructuralMap` publicly exposes the original small model and structure
map. `MorphismDefs` publicly exposes the derived adjunction, pullback square and mate
constructions needed in the statement. The private presentation import supplies the
source colimit and restriction equations; derived continuity makes the target cocone
colimiting; uniqueness identifies the comparison with the mate. No mathematical API is
changed and no consumer proof needs adaptation. The DAG already records exactly these
two proof dependencies, so its statement, attachment, proof and unit route stay intact.

## Users

`tools/downstream.py` reports the item as an unknown module because it is quarantined.
A complete live Lean import scan finds zero direct importers. The preserved quarantine
archive has these three direct consumers. No consumer is deleted or restored as part of
this item; their separate restoration assignments remain independent. A DAG-parent scan
also finds the fourth parent below, whose Lean source is absent from the active tree.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | V8 (dispatcher assignment) | Restore header; signature and full proof unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | quarantined | Same theorem application and statement; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | quarantined | Same theorem application and statement; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | quarantined | Same theorem application and statement; no adaptation. |
| Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange | absent active source, DAG parent | Dependency and statement preserved; no adaptation. |

## Status

landed 20261021T165946-L-2315925 2026-10-21 (merge of deliver/V8/Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology)
