## What changed

Retained the existing proofs of the five lower declarations in
`Sheaf.RingTheory.KoszulRegularSequenceDualComplex` and documented the two remaining
DAG-backed proof obligations with comments at their named theorem proofs. No public
signature, definition, or import was changed.

## Proved and sorry left

The following declarations are proved in the delivered module:

- `ExteriorAlgebra.exists_unique_koszul_conormal_comparison`;
- `ExteriorAlgebra.koszul_conormal_comparison_cohomology`;
- `ExteriorAlgebra.exists_koszul_quotient_augmentation`;
- `ExteriorAlgebra.koszul_conormal_comparison_change_generators`.

The existing named hole remains:

- `ExteriorAlgebra.koszul_conormal_comparison_localization`, node
  `lem-sc-koszul-regular-sequence-dual-complex`.

The two decomposition holes are:

- `ExteriorAlgebra.intrinsic_ext_determinant_multiplication`, node
  `lem-sc-koszul-ext-determinant-multiplication`;
- `ExteriorAlgebra.intrinsic_ext_determinant_roof`, node
  `lem-sc-koszul-ext-determinant-roof`.

(The module's node records all six declarations.)

## No longer needed

No imports or proof-dependency nodes were removed. Every listed import is used by the
statements or by the five completed proofs.

## Where the brief, the DAG or earlier work was wrong

No error in the statement or DAG plan was identified. The two remaining obligations
are precisely the intrinsic determinant assembly and localization compatibility steps
in the node's proof plan.

## New nodes

The intrinsic determinant proof was decomposed into two strict parts in the same
module: `lem-sc-koszul-ext-determinant-multiplication` records quotient-linearity,
and `lem-sc-koszul-ext-determinant-roof` records the normalized roof formula. The
parent theorem combines these two named parts. Both are intentionally left as
named `sorry` theorems with the source Tag 0BQZ and complete decomposition rationale
in their docstrings.

## Earlier second reading (a previous round; superseded)

The decomposition is reviewed against the parent statement: the multiplication node
supplies only the quotient-linearity clause, while the roof node supplies only the
normalized roof clause. The parent combines them by a direct existential conjunction;
no target statement is weakened. The existing localization hole remains unchanged.

## Second reading by Q3

1. Compared the delivered module with the repository version. Existing declaration
   signatures and definitions are unchanged; only proofs, documentation, and the two
   named decomposition declarations were added.
2. Compiled the module with `lcompile.py`; it succeeds. The only remaining `sorry`s are
   the two named decomposition theorems and the pre-existing localization theorem.
3. Checked the split statements and their node records. Each is a strict clause of the
   parent determinant assertion, has a Tag 0BQZ source, and does not duplicate an
   existing library declaration.
4. Checked the proof route and imports. The parent combines the two clauses directly,
   while the previously proved comparison, cohomology, augmentation, and generator
   change results remain in use; no unused imports were found.
5. Checked the unit route and DAG agreement. The parent node and both split nodes retain
   the unit `sk-thm-picard-duality` route, and the Lean declarations match their node
   statements. Verdict: suitable for delivery with the three documented holes left.

I changed only the report by adding this second-reading record; no further Lean repair
was needed.
