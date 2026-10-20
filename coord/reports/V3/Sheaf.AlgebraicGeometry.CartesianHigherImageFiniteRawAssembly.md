## What changed

Withdraw Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly, as assigned by
its `retire` queue entry, and its sole unclaimed importer
Sheaf.AlgebraicGeometry.CartesianRawClassChartNaturality. The latter has no importers.
Both modules are already proved and duplicate existing proved upstream modules.
The two paths are in deleted.txt; the delivery tool leaves empty modules.

The retained upstream theorems are
AlgebraicGeometry.Etale.exists_cartesianHigherImage_finite_raw_assembly and
AlgebraicGeometry.Etale.cartesianRawClass_chart_naturality. Each upstream statement omits
only the unused limit witness hc; each proof omits only the corresponding `have _ := hc`.
The private assembly helpers are identical. No upstream file is changed, and no proof
is replaced by sorry. There are no retained consumer adaptations.

Change record: coord/changes/retire-cartesian-higher-image-finite-raw-assembly.md.

## Proved and sorry left

The assigned item starts with 0 sorries. Closed: none (0). Added: none (0).
Sorries left in either withdrawn module: none (0). This is duplicate retirement,
not a new proof or decomposition.

A scratch #print axioms of the existing upstream assembly reports exactly propext,
Classical.choice and Quot.sound (2.2 seconds). Its argument uses the finite commuting
wide cospan and raw transition composition, including the empty-family case. The upstream
naturality proof is the identical transition-composition and chart-lift argument. Removing
the unused limit witnesses does not change either conclusion.

The initial one-import consumer redirection compiled in 11.0 seconds and passed a full
dry-run compile, axiom probe and preflight. Later compile attempts timed out; a profiled
scratch copy compiled in 11.7 seconds (elaboration 275 ms, tactics 798 ms, type checking
7.7 seconds), and an unprofiled retry took 58.6 seconds. These timings prompted a check
of whether retaining that duplicate consumer was necessary. The downstream tool confirms
it has no importers. The final delivery retires it together with its sole dependency,
so no changed proof or expensive definition is delivered. No limit is raised and no
proof or file is split. All profiling and audit commands remain only in scratchpad.

## No longer needed

Pruned modules:
Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly;
Sheaf.AlgebraicGeometry.CartesianRawClassChartNaturality.

The first module's two public imports (WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
and WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility) and proof
imports (WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal and
WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc) disappear only from this
redundant copy. The retired consumer's public import
WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback and private imports
Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality and
Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly also disappear.
Their other uses remain; no additional module or dependency node is claimed pruned.

Neither retired module nor either public theorem has a matching DAG attachment. The
parent node lem-sc-cartesian-higher-image-finite-raw-class-vanishing is attached to the
upstream parent, which already uses the upstream assembly. The upstream chart representative
already calls the upstream naturality theorem. The common-stage and chart-naturality
steps remain proved by those existing copies. Unit sk-thm-vanishing and all realized
entries are untouched.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but the assigned queue entry is a retirement
with zero holes. The earlier G2 report already records the helper-node attachment gap.
No new mathematical fact is introduced, so no new node is needed.

The downstream check gives one importer of the assigned module and zero importers of
its redundant Sheaf consumer. Searches of both Lean roots find no imports of either
Sheaf module outside the withdrawn pair. The only textual uses of their theorem names
in Sheaf are the declarations themselves. The corresponding upstream modules and all
upstream consumers remain unchanged under the source-library boundary.

msearch.py searches found IsCofiltered.wideCospan directly through Loogle and related
finite-cone results through Lean Finder. Local library searches located both upstream
replacements. No statement, definition, axiom, sorry or split-off node is added.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
