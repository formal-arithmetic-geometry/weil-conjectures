# AlgebraicGeometry.ProEtale.RationalP1.unitInversions and counitInversion

## Reason

The expanded inversion propositions make the kernel repeatedly compare large
instances of the derived categories after specialization to the rational coefficient.
A staged check accepts the coefficient, predicate and preservation arguments in
less than a second of kernel checking, then times out on the inversion arguments.
The complete file exceeded 120 seconds; a diagnostic with 50,000 heartbeats reports
a kernel deterministic timeout at the final application.

Name precisely the existing inversion conditions in two generic definitions, and
use those names both in the inversion clauses and in the parametric construction.
This caches the instance expressions. The two propositions are definitionally
identical to their previous formulas: there is no change of hypothesis or conclusion.
All preexisting data definitions and all target statements are unchanged.
The new definitions contain real proposition expressions and no proof holes.

The required direct-importer check also found a kernel timeout in the unclaimed
`Sheaf.Paper.AffineLineAdjunctionAssembly`: its original public proof exceeded
120 seconds; a diagnostic with 30,000 heartbeats identifies kernel checking of
`rationalP1_adjunction_assembly` (29.2 seconds before timeout). Its private
localization constructor checks quickly. Keep that constructor unchanged and
construct the canonical data over abstract localization records with an arbitrary
propositional conclusion in a proved private helper. The public theorem supplies
the original records. A second proved private helper extracts the triangle
theorem’s adjunction clause over the abstract records, through the existing generic
`Exists.nonempty` theorem. This keeps the large conjunction away from the concrete
localization instances. A generic categorical conversion produces the normalized
completed arrow. A small elaborator application forwards the existing source
specification’s arguments, preserving the source’s cached instance proofs instead
of re-elaborating the large predicates with different instance expressions. The
resulting term is kernel checked. Its signature and proof route are unchanged,
and it adds no hole. On the repair's renewed server check, the native bridge was
still the expensive step. Give it the six derived-category instances and Ext instance
directly, removing the unused field, geometry and localization-record assumptions.
The combined assembly still took 64 seconds, so move this self-contained fully proved
step into `Sheaf.Paper.RationalP1CompletedLimitBridge`, after the preceding definition
and context improvements, as the brief's final splitting step permits. The assembly
imports the public `completedLimit_exists` theorem privately. Its node records the
new proved dependency. No module held by another group is edited.

## Old

```lean
theorem unitInversions (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
    IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M.obj) ∧
    IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M.obj))

theorem counitInversion (K : rationalLocalizingCategory (coefficient l c).X Y) :
    IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y) K.obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
        (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
```

## New

```lean
theorem unitInversions (M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y)) :
    UnitInversionCondition (coefficient l c).X Y (line l c)
      (secondLineComparison l c k p hpl Y) M.obj

theorem counitInversion (K : rationalLocalizingCategory (coefficient l c).X Y) :
    CounitInversionCondition (coefficient l c).X Y (line l c) K.obj
```

`Sheaf.Paper.RationalP1UnitInversionCondition` defines `UnitInversionCondition`
as exactly the original conjunction. `Sheaf.Paper.RationalP1CounitInversionCondition`
defines `CounitInversionCondition` as exactly the original projection condition.
Both are public imports because the statements use them. The item node records
the two definition dependencies. Independent review can unfold these definitions
to verify the original formulas verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalP1UnitCounit | C1 | Uses the identical cached conditions; proves existence and uniqueness. |
| Sheaf.Paper.RationalP1KernelContractions | E2 | Direct importer; compiled unchanged. |
| Sheaf.Paper.AffineLineAdjunctionAssembly | unclaimed | Public signature unchanged; assemble over abstract localization records and use the proved completed-limit bridge. |
| Sheaf.Paper.RationalP1CompletedLimitBridge | new (C1) | Fully proved native extraction with only the required category instances; no new hole. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Direct importer; compiled unchanged. |

The source-only downstream scan found 232 transitive importers and no external
textual uses of either changed declaration name. The table lists the actual item,
its three direct importers and the new proved bridge; these are compiled against this delivery. No module
held by another group has been adapted, and the new helper definitions have no preexisting consumers.

Validation on the renewed server check: the item and its four comparison/condition
modules passed without errors or warnings; the item's reported elapsed time was
55.4 seconds. The unchanged kernel and triangle importers passed against it. The
final bridge/assembly pair passed together with exit code 0 and no warnings. The
assembly's original public signature and localization constructor were compared
with the current source and are unchanged. Seven Lean files are delivered; all
profiling options and temporary diagnostic sources have been removed.

The reviewed delivery `98beae7571e` was returned only because its reviewer-fix
filename did not match the landing protocol. This record is delivered at
`coord/changes/C1-rational-p1-inversion-condition-cache.md`. If a reviewer edits
it through `--apply-fixes`, `tools/batch_land.py` expects the flat fix filename
`C1-rational-p1-inversion-condition-cache.change.md` (the delivered stem followed
by `.change.md`), not the original `.md` basename. The delivery already contains
the complete record; no reviewer override is required to include it.

## Status

landed 20261026T235837-L-1460279 2026-10-26 (merge of deliver/C1/Sheaf.Paper.RationalP1UnitCounit)
