## What changed

Retired Sheaf.AlgebraicGeometry.NormalConstantGenericUnit in favour of the already proved
WeilConjectures.AlgebraicGeometry.NormalConstantGenericUnit, as assigned by the retirement
queue. The public declaration AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit
has a verbatim identical signature in both files. Its node is preserved and now attaches to
the adopted theorem. The node proof follows that theorem's full strict-localization model,
without the duplicate's private small/full transports.

Change record: coord/changes/D2-normal-constant-generic-unit-retirement.md.
Withdrawal: lean/Sheaf/AlgebraicGeometry/NormalConstantGenericUnit.lean in deleted.txt.
No upstream file or consumer source changes.

Validation through lcompile.py: the adopted module and the unchanged adopted consumers
NormalConstantOpenUnit, ConstructibleModuleIntegralStalkEmbeddingNoetherian, and
ConstructibleSheaf.FinitePushforward compile individually. An exact-statement application
probe importing the first two consumers also compiles (3.2 seconds). Its #print axioms checks
for isIso_unit_constantSheaf_generic_unit, isIso_unit_constantSheaf_open_unit, and
exists_integral_lowerStar_stalk_injective_noetherian each show only propext, Classical.choice,
and Quot.sound. FinitePushforward's separate compile took 13.4 seconds.

## Proved and sorry left

The assigned module starts with zero holes. Holes closed: 0. Holes added: 0. Holes left: 0.
No split-off statements. The existing complete adopted proof of
AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit supplies the retained node.
This delivery is a duplicate retirement, not a newly closed proof hole.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.NormalConstantGenericUnit, including its private
small_toBase, normal_indEtale_local_domain, normal_strict_generic_fibre_chart,
normal_strict_generic_fibre_integral, module_connected_sections, and
isIso_constant_unit_stalk_of_connected_strict_fibre. The adopted full-model module retains
its own complete argument and public theorem.

The withdrawn copy's imports are removed with it:
WeilConjectures.ConstructibleSheaf.Defs;
WeilConjectures.AlgebraicGeometry.ConstantStrictFibreStalkComparison;
WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap;
WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain;
WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal;
WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale;
WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections.
This does not withdraw these adopted modules or their statements.

The direct small-model proof dependencies def-weil-pbc-strict-henselization-limit and
def-weil-pbc-strict-henselization-structural-map are removed from this node's proof plan:
the adopted chart theorem and comparison already supply the full structural maps it uses.
Their nodes and modules remain; no claim is made that the wider library stops using them.
The other six proof dependencies remain, and every parent mathematical dependency and the
unit's realized route remain valid.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item, but the current item is a zero-hole
retirement repair. The retirement TSV lists two historical Sheaf importers; both have
already been retired. Current source and quarantine searches find zero importers of the
copy; tools/downstream.py --uses also reports zero downstream modules. The adopted consumers
already import the adopted generic theorem. No rework row or current D2 return concerns
this item.

All three DAG parents were checked: lem-weil-pbc-normal-constant-generic,
lem-weil-pbc-normal-constant-generic-open-unit, and
new-lem-weil-pbc-noetherian-integral-stalk-embedding. They continue to use the same node and
unchanged theorem, now supplied by the adopted module. This is retirement with a complete
replacement argument, not withdrawal justified merely by having no Lean importers.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
