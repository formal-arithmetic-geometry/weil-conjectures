## What changed

Retire Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso as assigned
by coord/retire-items.tsv. Preserve its distinct original-model theorem, with its
complete four-factor proof, in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyComparisonIso under
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselizationCohomologyComparison.
The old path is listed in deleted.txt. Update the existing comparison node's Lean
attachment to the retained theorem; its statement and proof dependencies stay unchanged.
The proof text now describes the repaired definitional-conversion step.

The old and adopted theorems have the same public name but different scheme models.
Keeping an explicit smallModel_ name follows the landed predecessor repair in
coord/changes/A3-retire-strict-local-global-homology.md and preserves the four-factor
map rather than silently replacing it with the strictLocalization comparison.

Change record:
coord/changes/B5-retire-strict-henselization-cohomology-comparison.md.

Repair of return 95339d037: removed the duplicate private theorem
AlgebraicGeometry.Etale.map_mate_eq_mappedMate from the retained module.
Its only call is replaced by `change IsIso (mappedMate _ _ _ _ _ _)`.
The equality was reflexivity of a private definition, so definitional conversion
suffices without an extra theorem or import. The upstream helper itself is private.
This removes the duplicated statement rather than renaming it. The DAG proof text
now records definitional conversion instead of the deleted helper equality.
The public theorem's signature and all four isomorphism factors stay unchanged.

Validation: repaired module compiled cleanly on the server in 5.4 seconds.
The current-source downstream check reports zero downstream modules and no external
uses of the renamed declaration. The combined module compile also passed (4.8 s).
The compatibility probe compiled cleanly (2.0 s), importing the small-model theorem,
the adopted comparison theorem and the adopted parent together and applying the
adopted comparison theorem. Delivery preflight follows.

## Proved and sorry left

Actual hole count: zero before, zero after. Holes closed: zero. Holes added: zero.
Split off: zero. No declaration is left with sorry.

The complete existing proof of
AlgebraicGeometry.Etale.isIso_strictHenselizationCohomologyComparison is retained
under the smallModel_ name (node
lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison). It is not counted
as a new proof or a decomposition. This delivery repairs the colliding module and
public name; it does not claim to eliminate the proof dependencies' remaining holes.

## No longer needed

Withdrawn module:
Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso.
Its mathematical theorem remains needed and realized in the new small-model module.
No mathematical node, parent edge, unit step, or proof dependency is pruned.
The retained module keeps all four public statement imports and its private
BaseChangeGlobalHomology proof import. The duplicate private reflexivity theorem
map_mate_eq_mappedMate is no longer needed; its statement is not recreated.

Source and quarantine searches found zero importers or external uses of the item.
The historical listed Sheaf parent is already withdrawn. Its DAG parent still cites
the comparison node, and that edge is preserved with the retained realization.
The adopted parent uses WeilConjectures.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso
and needs no edit. No adopted declaration, public import, attribute or signature changes.

## Where the brief, the DAG or earlier work was wrong

The dispatch text describes a proof item, but the current item has no sorry and is
listed as a DIFFERENT retirement repair. The return correctly identified a duplicated
private reflexivity helper, now removed. The retirement row's API shorthand mentions
a private helper; the decisive public difference is strictHenselizationScheme versus
strictLocalization. Directly substituting the upstream theorem would change the map.
The historical consumer listed in that row is now an empty withdrawn module, while
its DAG attachment remains stale. Neither fact permits discarding its comparison
obligation, so this delivery preserves the complete original-model theorem.

Read the H3 restoration record, A3 predecessor retirement, current item and upstream
twin, current and adopted parent, the comparison and parent DAG nodes, unit sk-thm-br,
and Stacks etale-cohomology.tex at theorem-higher-direct-images and remark-stalk-fibre.
The source asserts the unrestricted comparison for qcqs f and arbitrary abelian F;
no torsion, nonemptiness or positive-degree hypothesis is introduced. The retained
signature is identical except for its unambiguous theorem name, so q = 0, zero sheaves
and empty X retain their original statements and proof.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
