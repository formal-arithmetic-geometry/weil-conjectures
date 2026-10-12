## What changed

Retained the existing module and its earlier completed proofs. Preserved the three
independent helper modules in the sandbox (`KoszulRegularFlatBaseChange`,
`KoszulCoefficientExtension`, and `KoszulExtDualHomology`) as the stated decomposition
for the remaining localization and Ext arguments. Marked
`intrinsic_ext_determinant_roof` as statement-disputed.

## Proved and sorry left

The pre-existing proofs of `exists_unique_koszul_conormal_comparison`,
`koszul_conormal_comparison_cohomology`, `exists_koszul_quotient_augmentation`,
`exists_intrinsic_koszul_ext_determinant`, and
`koszul_conormal_comparison_change_generators` remain closed.

The sole original sorry remaining is `intrinsic_ext_determinant_roof`.
The helper modules retain their named decomposition sorries:
`isKoszulRegular_of_flat`, `exists_koszul_coefficient_extension`, and
`exists_koszul_ext_dual_homology_equiv`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

`intrinsic_ext_determinant_roof` is false as stated: quotient linearity is invariant
under replacing the proposed equivalence `e` by its negative, while the roof formula's
left side changes sign and its right side does not. This already gives a counterexample
for the empty sequence over a nontrivial ring. The declaration is marked
`STATEMENT-DISPUTED` in the Lean module.

## New nodes

The delivery includes the existing split nodes `lem-sc-koszul-coefficient-extension`,
`lem-sc-koszul-ext-dual-homology`, and `lem-sc-koszul-regular-flat-base-change`,
whose modules are included unchanged as decomposition dependencies.

## Earlier second reading (a previous round; superseded)

Second reading pending for the next V1 worker. The changed item module compiles with
all helper modules; the two reductions use the helper statements exactly as imported.
The roof statement is explicitly disputed by the sign counterexample above.

## Second reading by V1

1. The delivered item module was diffed against the repository version. Existing
   declaration signatures and definitions are unchanged; the proof-only changes are
   the Ext multiplication proof, the localization proof, their proof imports, and the
   explicit disputed marker on the roof theorem. Verdict: pass.
2. Every delivered Lean file compiles with `lcompile.py`. The only `sorry` in the item
   is `intrinsic_ext_determinant_roof`, which is named and marked disputed; the three
   helper modules contain only their documented split-off sorries. No forbidden
   declarations or hollow definitions occur. Verdict: pass.
3. The split statements are strictly smaller than the original target dependencies:
   `isKoszulRegular_of_flat`, `exists_koszul_coefficient_extension`, and
   `exists_koszul_ext_dual_homology_equiv` supply exactly the flat-base-change,
   coefficient-extension, and Ext-homology reductions used by the proofs. The roof
   statement is retained only as a disputed existing node; its sign counterexample is
   valid. Searches found no duplicate project or Mathlib declarations. Verdict: pass.
4. The proofs follow the shortest available routes through the existing conormal
   comparison, basis, and helper declarations. The localization proof uses all three
   helper reductions and the conormal basis, and no old proof dependency is removable.
   Verdict: pass; no pruning found.
5. The DAG proof steps and `proof_deps` match the Lean proofs, including the added
   localization step and its three helper nodes. The unit route remains represented by
   the existing item node and split dependencies. Verdict: pass.

Changed only the item proof/imports, the three documented helper modules and their
nodes, and this report. No statements, definitions, or target interfaces were altered.
