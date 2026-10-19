# Split/attachment: def-weil-pbc-ind-etale-basis

1. Files written: updated item split metadata only; no new nodes.
2. Attachments: `AlgebraicGeometry.Scheme.AffineProEt`, `AlgebraicGeometry.Scheme.instCategoryAffineProEt`, `AlgebraicGeometry.Scheme.AffineProEt.toProEt`, `AlgebraicGeometry.Scheme.AffineProEt.precoverage`, and `AlgebraicGeometry.Scheme.AffineProEt.topology` belong to `def-weil-pbc-ind-etale-basis`.
3. WANTED: none.
4. No statement discrepancy. The source definition is realized by the affine pro-etale category, its category instance, the inclusion into the pro-etale site, and the induced precoverage/topology. The affine ind-etale characterization is supplied by `AlgebraicGeometry.proAffineEtale_iff_appTop` for affine source and target; no extra finiteness, covering, or coefficient hypothesis is added.
5. Nothing remains to split. This attachment is supported by sorry-free declarations in slopmaster2; the item is now marked split so the delivery preflight can record the reviewed definition.

## Review by NE

I re-read the imported blueprint definition and rebased the dependency citation against the current DAG. I read the current statement of `def-weil-pbc-ind-etale-algebra`, including its filtered-colimit ind-etale clause, affine inverse-limit clause, and weakly-etale equivalence, and verified that the item uses only the ind-etale clause. I also re-read `def-weil-pbc-proetale-site` for the ambient site and induced coverings. I read the imported blueprint definition at `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-ind-etale-basis.md`, the chapter and unit records, and the source file `WeilConjectures/AlgebraicGeometry/ProEtale/Comparison/Affine.lean`. `AffineProEt` (lines 88–91) defines the affine pro-etale objects as the `proAffineEtale` objects over `S`; `instCategoryAffineProEt` (lines 101–102) supplies their category; `toProEt` (lines 134–136) is the inclusion into `S.ProEt`; `precoverage` (lines 278–280) pulls back the pro-etale precoverage; and `topology` (lines 379–382) is the restricted pro-etale topology. The object instance `AffineProEt` gives affine schemes (line 129), while `proAffineEtale_iff_appTop` in `WeilConjectures/AlgebraicGeometry/Morphisms/ProAffineEtale.lean` (lines 335–341) identifies the affine objects over affine `S` with ind-etale maps on global sections. Thus every clause of the item is covered under its affine-base hypothesis. I checked the slopmaster2 sorry map entries: all five attached declarations have `s=false` and `ts=false`; the upstream-master declarations were not used as proof. The empty affine scheme and identity object introduce no exceptional case, and no statement or dependency was changed. No citations.json is needed because there are no proof steps.

## Second reading by NE

- Item statement: checked hypothesis by hypothesis against Stacks `proetale.tex` Tags 097I (`definition-ind-etale`) and 0990 (`lemma-proetale-enough-w-contractible`), and against the two definition dependencies; the affine object condition, ind-etale condition, full-subcategory condition, and induced coverings all agree.
- Proof steps: there are no proof steps (`proof=[]`), so there are no uncited uses or elementary-step claims to check.
- New nodes: there are no new nodes; B1--B7 and duplicate-node checks are vacuous.
- Edge cases: the zero ring/empty affine scheme, a field base, the identity affine object, and empty or singleton covering families introduce no extra hypothesis or exception; the definition remains the stated full subcategory with inherited coverings.
- Attached declarations: re-read `AffineProEt`, its category instance, `toProEt`, `precoverage`, and `topology` in `AlgebraicGeometry/Scheme/AffineProEt`; re-read `proAffineEtale_iff_appTop` for the affine ind-etale characterization. All five declarations are sorry-free in the slopmaster2 audit.

Changes made: replaced the blueprint-only source entry with the Stacks document and tags 097I/0990, so the provenance names the source definition and affine-basis clause explicitly. No mathematical statement, dependency, or proof metadata was changed.
