# Stage 1 report: lem-trf-finite-residue-point-closed-in-fibre

1. **Files written.** The item file `dag/nodes/sec-trace-formula/lem-trf-finite-residue-point-closed-in-fibre.json` was copied from the current shared DAG and split in place. No new DAG nodes were created. `citations.json` records verbatim statement quotes for all cited nodes. The item is marked `split`; its Mathlib searches remain recorded from the required search commands and found only a more general closed-singleton criterion, not this relative finite-residue statement.
2. **Attachments.** None. I searched both `/home/ubuntu/weil-newtargets-master/WeilConjectures` and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, blueprint tag, and the finite-residue/closed-fibre wording; no exact sorry-free project declaration exists.
3. **WANTED.** None.
4. **What was checked or corrected.** The imported statement agrees with Stacks Project `literature/stacks-project/morphisms.tex`, Tags 01TE and 01TF, and I retained its hypotheses and conclusion. The proof now follows the affine-local argument instead of leaving the item unsplit. I read the chapter and unit records, the item source, and every cited node file. Existing converse statements about isolated fibre points and finite residue extensions were read and are not duplicates of this finite-implies-closed direction.
5. **Unfinished.** Nothing remains unfinished in this stage-1 split.

## Not duplicates

`lem-trf-finite-residue-point-closed-in-fibre` vs `lem-weil-pbc-isolated-fibre-point-residue-finite`: this item proves finite residue extension implies closedness in the fibre; the existing node proves the converse implication from an isolated fibre point to finite residue extension.

`lem-trf-finite-residue-point-closed-in-fibre` vs `lem-weil-pbc-lft-over-field-isolated-point-residue-finite`: this item is the finite-to-closed direction for an arbitrary base fibre; the existing node is a converse criterion for an isolated point over a field.

## Review by ND

I checked the source paragraph in `morphisms.tex` at Tags 01TE and 01TF. The item’s finite extension is algebraic, and the source reduces closedness in the fibre to an affine neighbourhood and the maximal-ideal argument. The statement’s fibre and residue-field dependencies were retained exactly.

For step 1, I read `def-pc-scheme-fibre` and used its fibre-product description and second projection to `Spec κ(s)`. I read `lem-weil-pbc-lft-base-change`, whose statement applies to any base change of a locally finite type morphism, so it supplies local finite type for `X_s → Spec κ(s)`. For an arbitrary specialization `y` of the induced point `ξ`, I chose an affine open containing `y`; stability of opens under generalization gives `ξ` in the same open.

For step 2, I read `lem-weil-pbc-lft-affine-pairs` and `def-weil-finite-type-morphism`. Together they justify that the chosen affine open is of finite type over the field `κ(s)`: its coordinate algebra is finitely generated and the affine source is quasi-compact. I read `lem-sbc-scheme-fibre-stalk-quotient`; its stated local-ring quotient, applied at `x` over `s`, identifies the fibre local ring with the quotient by the base maximal ideal. Passing to maximal ideals gives the same residue field `κ(x)` and the same `κ(s)`-map. I read `lem-weil-pbc-residue-field-point-naturality`; its open-immersion clause identifies this residue field after restricting from the fibre to the affine open. Finally I read `lem-kun-closed-point-field`; clause (a) says that a point of a finite-type scheme over a field is closed exactly when its residue field is finite over that field. The item’s finite-dimensional hypothesis therefore makes `ξ` closed in the affine open.

For step 3, I checked the specialization argument directly: every specialization lies in an affine open where `ξ` is closed, hence equals `ξ`; the standard scheme-topology criterion then makes the singleton closed. This is marked elementary and uses no uncited theorem. The two generic statements from other units (`lem-kun-closed-point-field` and `lem-sbc-scheme-fibre-stalk-quotient`) are explicitly declared as tool uses in `split_report`, because the trace-formula unit has no replacements for them.
