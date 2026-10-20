## What changed

Retired `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`, the duplicate
listed in `coord/retire-items.tsv`. Its node now attaches to the proved declaration
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_iso` in the upstream twin.

Adapted all five direct consumers: `KoszulSelfExtDualExteriorConormal`,
`KoszulSelfExtYonedaSurjection`, `Modules.ExteriorSheafFullOpenIso`,
`Modules.ExteriorSheafTopInvertible`, and `SelfTorConormalWedgeChartFromSections`
(all under `Sheaf.AlgebraicGeometry`). They privately import the upstream restriction
module and `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison`, rewrite the
result through `exteriorSheaf_eq_exteriorPower`, and retain their existing proof.
Each consumer node records this equality dependency. Every existing consumer public
signature and public import is unchanged. The source library is unchanged.

Change record: `coord/changes/retire-exterior-sheaf-restrict-iso-k4.md`.

Validation: all five adapted modules compile with `lcompile.py --all`; their
statements compare identically with the originals. No warnings or added holes.
`#print axioms` confirms that the upstream restriction theorem and the shared
exterior-sheaf equality use only `propext`, `Classical.choice`, and `Quot.sound`.
Searches: `msearch.py` LeanFinder found the generic restriction API, Loogle had
no `exteriorPower` match, and local `rg` found the exact upstream theorem and
the shared proved comparison used here.

## Proved and sorry left

This is a duplicate retirement with zero initial holes: **0 of 0 holes closed;
0 holes added; 0 split off; 0 holes left in any delivered module**.
The retained upstream `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_iso`
is already proved by packaging the mutually inverse hom data.
The five adapted theorems remain proved with unchanged statements:

- `AlgebraicGeometry.koszulRegularImmersion_self_ext_dual_exterior_conormal`.
- `AlgebraicGeometry.koszulRegularImmersion_self_ext_yoneda_surjection`.
- `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_fullOpen_pushforward_iso`.
- `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_top_isInvertible`.
- `AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_from_sections`.

No theorem with `sorry` is introduced or retained in this packet.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso` and removed its
private import from all five direct consumers. The duplicated private helpers
`exteriorSheafPresheaf_eq_exteriorPower` and `exteriorSheaf_eq_exteriorPower` in
that module are no longer needed; the existing public proved comparison supplies
the equality. No new module or node is created.

No mathematical node is discarded: `lem-sc-exterior-sheaf-restrict-iso` is retained
with the upstream attachment, as are all parent edges and unit steps. The restriction
node uses `lem-sc-exterior-sheaf-restrict-hom-data`; its former direct proof edge to
`def-sc-sheaf-exterior-power` is unnecessary for the simple packaging proof. That
definition remains a statement dependency. The upstream hom-data, open-pullback and
open-pullback-data declarations and their dependencies remain needed and unchanged.
The consumers additionally cite `lem-sc-exterior-sheaf-upstream-comparison`.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a module with unfinished proof obligations. At the
current source the item is already proved, with zero holes; its actual assignment
is the listed retirement. The F1 adaptation had copied two equality proofs into the
item, but K5's proved public comparison already provides them. Reusing that comparison
allows all callers to consume the existing upstream theorem directly. The API
mismatch is equality of constructions, not a weaker mathematical statement.
No target, definition, mathematical hypothesis, conclusion or unit route changes.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
