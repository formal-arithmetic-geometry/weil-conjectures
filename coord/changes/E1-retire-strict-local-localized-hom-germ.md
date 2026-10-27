# StrictLocalLocalizedHomGerm: retire the upstream re-export

## Reason

The current queue assigns retirement, not another proof split: coord/queue.tsv lists
this module as retire, and coord/retire-items.tsv names its upstream twin. The human's
policy is in coord/changes/retire-sheaf-twins-20261020.md. The current module has no
local declarations and zero holes: K1 already replaced its conflicting definitions
by a public re-export of the complete upstream implementation. Retiring this wrapper
now only requires a direct import in its sole live consumer.

The original-model DAG statement is a different interface. Its current attachment is
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm, declaration
AlgebraicGeometry.Etale.smallModel_sourceLocalizedSectionsIso_germ. Its source is
quarantined under that same SmallModel path (coord/rework.tsv). That implementation,
attachment, statement, dependencies, all five DAG parent edges and all unit routes
are preserved. The upstream strictLocalization theorem does not replace this theorem
about strictHenselizationScheme. The node copy changes only its lean.note to record
this distinction and this retirement.

## Old

The withdrawn module is, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm

/-! # Localized Hom classes and restriction of a complex on the base

The adopted source module supplies the constructions and the proved germ comparison
on `Scheme.strictLocalization`. Re-export it here so that neighbourhood restriction,
the canonical source germ leg, and the complex restriction all use the same scheme.

In particular this preserves the names `sourceLocalizedSectionsIso`,
`strictHenselizationSectionRestriction_naturality`, `strictLocalSectionRestrictionNat`,
`strictLocalComplexSectionRestriction`, and `sourceLocalizedSectionsIso_germ`.
It does not redeclare a second version of any of these constructions.

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ).
-/

@[expose] public section
```

The sole live consumer imported it privately:

```lean
import Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm
```

## New

Withdraw only lean/Sheaf/AlgebraicGeometry/StrictLocalLocalizedHomGerm.lean using
deleted.txt. The consumer imports the identical provider directly:

```lean
import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm
```

There is no declaration, definition, instance, visibility or statement change.
The import closure visible to this proof is the same: the old wrapper's only import
was this public upstream import. All upstream signatures, attributes, public imports
and proof bodies stay verbatim. No target needs a new semantic review for this
path-only import migration. No new theorem or proof hole is introduced.

## Users

The downstream.py census finds 13 live downstream modules and zero uses of
sourceLocalizedSectionsIso_germ. A direct import scan of lean/ and quarantine/
finds one live importer and one archived importer of the retiring wrapper.
No relevant module has a holder file in the shared coord/claims inventory.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm | E1 | Withdraw the zero-declaration wrapper. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | unclaimed | Sole live importer: change only its private import; complete statement and existing proof hole unchanged. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Transitive consumer; identical provider remains available. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnitGerm | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationCompatibility | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalComplexSectionsMate | quarantined; unclaimed | Historical direct importer, absent from lean/: archive and rework assignment preserved. Its upstream twin imports the upstream provider; its SmallModel counterpart uses the retained SmallModel provider. No restoration or deletion of this different item is attempted. |
| Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate | unclaimed | Historical listed consumer now re-exports its upstream twin and no longer imports this wrapper. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | quarantined; unclaimed | Current DAG realization, completely preserved at its quarantine path with all dependencies. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | quarantined; unclaimed | DAG parent still uses its original-model realization; no edit or dependency removal. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | quarantined; unclaimed | DAG parent still uses its original-model realization; no edit or dependency removal. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | quarantined; unclaimed | DAG parent imports the retained SmallModel provider; unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | quarantined; unclaimed | DAG parent imports the retained SmallModel provider; unchanged. |
| WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm | adopted source; unchanged | Complete canonical implementation retained verbatim. |

The fifth DAG parent is the live ordinary-germ consumer above. Its mathematical
edge to the original-model lemma stays, even though its unfinished proof currently
imports the canonical API. This retirement makes no claim to solve that separate
proof obligation. The unit sk-prop-h2 has no realized statement or step referring to
this wrapper, and its route is unchanged.

Validation: lcompile.py compiles the adapted live consumer successfully (3.2 s).
The only source change in it is the import line. A separate import-only probe checks
all five upstream public names and prints the axiom lists of both comparison
theorems. Delivery preflight and the maintainer's global build check the packet.

## Status

landed 20261022T143117-L-961379 2026-10-22 (merge of deliver/E1/Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm)
