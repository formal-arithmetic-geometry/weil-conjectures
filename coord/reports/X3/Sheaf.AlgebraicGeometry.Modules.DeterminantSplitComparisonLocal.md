## What changed

Repaired the determinant restriction item using the corrected interface already present in the
module: the equivalences `d` are pointwise equal to a natural linear family `dNatural`. The proof
now explicitly chains the two substitutions with the naturality hypothesis `hn`. The unconstrained-`c` interface identified in upstream review #1428 was already repaired in
the repository; this delivery preserves that repaired interface and uses no arbitrary lift family.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction` is proved. There are
zero `sorry`s left and no new holes were added. Holes closed by this delivery: none; the
repository version already contains a proof of this declaration. Holes added: none. This is a
queued repair and import pruning, with one of one theorem proofs checked, not net hole progress.

## No longer needed

Removed direct imports:

- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`, replaced by
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, which supplies the monoidal instance
  needed in the statement. No tensor-section declarations are used.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`; no local-freeness
  hypotheses remain in the current statement.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`, replaced by
  `Mathlib.Algebra.Homology.ShortComplex.Basic`, which supplies `ShortComplex`.
- `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`; no biproducts occur here.

The old node has empty `proof_deps`, so no proof-dependency nodes are retired. No Sheaf module
is claimed globally pruned. The sole direct importer, `DeterminantSplitComparison.lean`, already
imports all four removed modules itself. All remaining imports support the public statement.
No additional DAG nodes or modules are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report treated this assignment as stale and did not deliver a changed module.
The upstream false statement was the version with an unconstrained family `c`; the current repaired
statement replaces it with a natural linear family `dNatural` and pointwise equality `hd`, which is
sufficient for restriction naturality. The existing caller in
`DeterminantSplitComparison.lean` supplies exactly these hypotheses.

## Second reading by X3

1. Compared the complete delivered module against the repository with `diff`. PASS: the existing
   declaration signature and docstrings are byte for byte unchanged; no definitions or target
   statements changed. Only its proof and imports differ. Read the existing interface-change
   records: this delivery does not reinstate any superseded interface.
2. PASS: compiled the proof locally through `lcompile.py`. The scratch copy of the final pruned
   module with `#print axioms` compiled and reported exactly `propext`, `Classical.choice`,
   `Quot.sound`. There are no `sorry`s, definitions, added declarations or forbidden constructs.
   Each step substitutes `hd` at the indicated open, with `hn` giving the middle equality.
3. PASS (no split-off statements): no new holes or nodes. Checked empty opens, zero ranks and
   zero rings mathematically: the proof is equality substitution and imposes no positivity,
   nonemptiness or nontriviality assumption. Checked the existing caller, which supplies the
   natural family and definitional pointwise equality. A local library search found only this
   theorem and its caller; no auxiliary result is needed for this elementary argument.
4. PASS: the existing shorter rewrite route and the delivered explicit chain prove the same
   proposition by equality substitution. Kept the first worker's correct explicit chain.
   Pruned the unused imports and narrowed the two dependency imports listed above; compilation
   confirms the remaining imports suffice. Read `dag/units/sk-thm-picard-rr.json`: this elementary
   node is not a realized unit statement or step; neither its unit route nor any realized entry
   is changed. No old `proof_deps` remain unreported (the list is empty).
5. PASS: `new-determinant-split-restriction` records precisely this signature, the substitution
   argument, empty `proof_deps`, and the corresponding elementary proof origin. No node update
   is necessary, and there are no new nodes to validate.

Second reading changed the imports and corrected the report's attribution and hole accounting.
The first worker's proof is unchanged. The final delivery is a queued repair of an already proved
statement, with zero holes closed and zero added.

Import change record: `coord/changes/determinant-split-comparison-local-imports.md`.
