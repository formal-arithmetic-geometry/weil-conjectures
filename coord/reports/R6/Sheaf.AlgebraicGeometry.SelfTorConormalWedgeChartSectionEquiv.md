## What changed

Retired Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv, the duplicate
identified in coord/retire-items.tsv, in favor of the existing proved module
WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv. Its DAG node
now attaches to the upstream declaration with the upstream signature verbatim.

Adapted the sole direct consumer, Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart.
Its private import now selects the upstream module, and it imports
Sheaf.AlgebraicGeometry.ExteriorSheafComparison privately. Evaluating the canonical
comparison Scheme.Modules.exteriorSheafIsoExteriorPower on the chart gives a linear
equivalence between the section modules; exteriorSheafIsoExteriorPower_hom_wedge proves
that it preserves the canonical wedge (reviewer fix: this replaces a private re-built
copy of the comparison isomorphism).
Composing it with the upstream section equivalence supplies the input to the unchanged
affine sheaf reconstruction theorem. The consumer's public signature and public imports
are unchanged. Both node proof records describe the resulting route.

Change record: coord/changes/retire-self-tor-conormal-wedge-chart-section-equiv.md.

Validation: the adapted consumer compiles without warnings. An explicit
`#print axioms AlgebraicGeometry.exists_selfTor_conormal_wedge_chart` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; this includes the canonical comparison
and upstream section equivalence. The temporary print command is removed. Public
signature and public-import comparisons, line widths, node dependency unions, the
verbatim upstream attachment, and the overlaid import closure all pass their checks.
The required delivery dry run reports OK. Its auxiliary automatic axiom probe timed
out; the explicit axiom check above completed successfully in the same file.

## Proved and sorry left

This is a retirement repair with zero original holes. Holes closed: none (0 of 0).
Holes added: none. No sorry remains in any delivered Lean module; no statement was
split off. The upstream exists_selfTor_conormal_wedge_chart_section_equiv remains
unchanged and proved. The adapted exists_selfTor_conormal_wedge_chart is proved,
including the section-transport equation for every tuple.

## No longer needed

Withdrawn module and removed consumer import:
Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv.

The DAG node new-t2-self-tor-conormal-wedge-chart-section-equiv remains needed and
attaches to the upstream module. Its dependencies remain needed by the preserved
upstream proof: lem-weil-pbc-affine-conormal-sections,
new-q1-exterior-sheaf-affine-unit-bijective,
and new-q1-self-tor-conormal-exterior-section-model. The exterior-sheaf notion
def-sc-sheaf-exterior-power is removed from this node's proof dependencies but remains
a statement dependency. The consumer node's proof now cites lem-sc-exterior-sheaf-comparison
in place of def-sc-sheaf-exterior-power.
No other module or mathematical node is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module with a hole; the current assigned file
has zero holes and is an explicit retirement item. The retirement list's historical
PROOFDIFF_UNSAFE classification predates retirement of its shared dependencies.
The adapted consumer's current overlaid import closure has no Sheaf/upstream module
pair and no import of the withdrawn module.

The two signatures use different exterior-sheaf constructors, so changing the import
alone is insufficient. The canonical comparison lem-sc-exterior-sheaf-comparison handles that
difference without changing any public statement or definition. They work uniformly
in degree zero, on empty charts, and for zero quotient rings. There is no freeness,
regularity, or nonemptiness assumption. The unit route is preserved, and no adopted
source-library file is changed.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
