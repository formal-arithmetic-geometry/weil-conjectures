## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit.
The existing upstream twin proves the theorem for PresheafOfModules.exteriorPower.
Both direct consumers, Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent and
Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartSectionEquiv, now import it privately.
Each proves a private equality of the old and upstream exterior presheaves using uniqueness
of restriction maps on pure wedges, then transports the upstream affine-unit theorem.
Their public statements and definitions are unchanged. No upstream file is edited.

The affine-unit DAG attachment now points to the source theorem and records the transport;
the two parent proof plans record the same interface glue. The change record is
coord/changes/retire-exterior-sheaf-affine-unit.md. The item is withdrawn through deleted.txt.
Both adapted modules compile alone via lcompile.py, with no warnings. A source import-closure
scan finds no remaining import of the retired module and no Sheaf/source twin pair in either
consumer's environment. The original public signatures compare identical.

## Proved and sorry left

This is a retirement repair with zero initial holes: 0 holes closed, 0 holes added,
0 holes remaining in the delivered files; no statements split off.
The duplicate declaration AlgebraicGeometry.Scheme.Modules.exteriorSheaf_affine_unit_bijective
is retired in favor of its fully proved source-library declaration (node
new-q1-exterior-sheaf-affine-unit-bijective). Both private presheaf-equality helpers are
fully proved, as are the unchanged conclusions
AlgebraicGeometry.Scheme.Modules.isQuasicoherent_exteriorSheaf_of_isAffine and
AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_section_equiv.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/Modules/ExteriorSheafAffineUnit.lean.
Remove both consumers' private imports of Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit,
replacing them with WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit.
Its DAG node remains needed and is attached to the upstream theorem. No mathematical dependency
is pruned: affine basic-open localization, exterior-power localization and affine-localizing
presheaf sheafification remain used in the source proof. Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
remains needed by the unchanged consumer statements. No other module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a hole, but this current assignment is listed as retire
in coord/retire-items.tsv and has zero holes. The upstream statement uses a different presheaf
construction, so an import replacement alone does not preserve the consumers' proof terms.
The elementary equality proved from the existing unique pure-wedge restriction property
resolves that difference without changing any public statement or adding a hole. The mathematical
principal-localization argument and unit route are preserved.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
