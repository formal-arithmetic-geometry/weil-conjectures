## What changed

Proved `scalarUnit_abelianTranspose_section_normalized` in
`Sheaf.Paper.TowerScalarUnitAbelianTransposeSectionNormalized` without changing its
statement or `canonicalScalarUnit`. Private proved helpers handle forgetting section
maps, cancellation of the integer generator, scalar and geometric adjuncts on integer
sections, and the constant-integer direct-image formula. The proof reuses the existing
integral-forgetful full-faithfulness and push-evaluation lemmas. Updated the item's DAG
proof to match this argument. Added proof imports
`import all Sheaf.Paper.TowerRestrictedScalarAdjunction` for its private, proved
full-faithfulness and push-evaluation helpers and
`import all Sheaf.Paper.TowerLineTransitionTensor` for its heterogeneous additive
application lemma. All public imports are preserved.

Validation: the complete module compiled cleanly through `lcompile.py` in 23.8 seconds.
The existing theorem signature and canonical scalar-unit definition are unchanged.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.SpTowerClasses.scalarUnit_abelianTranspose_section_normalized`
(node `lem-sp-tower-scalar-unit-abelian-transpose-section-normalized`).
No holes added or split off; zero holes remain in the item.

## No longer needed

No existing imports, modules, or dependency nodes are withdrawn. The separate local
integer-lifting argument suggested by the original plan is unnecessary here: the existing
integral-forgetful full-faithfulness proof already supplies that argument, and
`SheafOfModules.unitHomEquiv` reduces the remaining cancellation to the image of one.
No root-line, Kummer-boundary, or derived-category comparison is used.

## Where the brief, the DAG or earlier work was wrong

The normalized statement is correct, including empty charts and zero coefficient rings.
The previous reductions stopped before the elementary cancellation and adjunction
calculation; this delivery completes them without another split. The source docstring's
blueprint label referred to the parent section node; corrected it to this item's node.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.TowerScalarUnitAbelianTransposeSectionNormalized": "63c67e61c0d9b779892a22af0526271c2363dfef"}, "results": {"Sheaf.Paper.TowerScalarUnitAbelianTransposeSection": {"hash": "973b7c9010a47802cb77c43492cbc0e357eadd01", "status": "OK"}}, "seconds": 76, "time": "2026-10-28T07:57:44+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
