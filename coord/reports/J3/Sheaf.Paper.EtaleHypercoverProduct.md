## What changed

`Sheaf.Paper.EtaleHypercoverProduct` now proves
`AlgebraicGeometry.isEtaleHypercover_prod` directly. In each degree it takes the product
of the two matching objects, constructs the lower-simplex projections, proves the matching
universal property on all objects of `Over X`, and constructs the matching map. Evaluation
and the étale forgetful functor preserve the needed binary products. The scheme map is
identified explicitly, after both projections, with the product of the two surjective
matching maps via `isoPullback`. `MorphismProperty.pullbackMap` proves its surjectivity.

The second reading replaced the first worker's per-degree restatement with this full proof.
The proposed new helper module, node and import-change record were removed before delivery.
The original theorem signature, visibility, public imports and definitions are unchanged.
The only added import, `Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`,
is a plain proof import. The existing node's proof metadata follows the direct proof.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.isEtaleHypercover_prod`
(node `lem-weil-pbc-hypercover-product`), the sole original hole in the item.
Holes added: none. Sorries left in the delivery: none. No decomposition or new theorem.
The proposed `AlgebraicGeometry.etale_hypercover_product_data` is withdrawn, not delivered.

Local single-file compilation succeeds with no warnings. A scratch copy with
`#print axioms AlgebraicGeometry.isEtaleHypercover_prod` reports exactly
`propext`, `Classical.choice`, `Quot.sound`; there is no `sorryAx`.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct`;
- `WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover`.

Every old proof dependency absent from the new proof is listed here:

- `def-weil-pbc-finite-split-hypercover`: use the existing `IsEtaleHypercover` definition;
- `lem-weil-pbc-matching-object-fibre-product`: construct the product matching universal
  property directly from the two hypotheses;
- `lem-weil-pbc-etale-covering-base-change`: use the Mathlib surjectivity-under-base-change
  instance (`lem-weil-pbc-surjective-base-change`), since arrows in `X.Etale` are étale;
- `lem-weil-pbc-etale-covering-composition`: composition of surjective scheme maps is
  already a Mathlib instance used by `MorphismProperty.pullbackMap`.

The old dependencies `def-weil-pbc-etale-site` and `def-pc-fibre-product` remain.
`def-weil-pbc-etale-hypercover` and the existing Mathlib leaf
`lem-weil-pbc-surjective-base-change` record the remaining inputs. This is pruning from
this item's proof/import closure; no claim about global unreachability is made.
The proposed `EtaleHypercoverProductData` module and node were never on the repository
baseline and are omitted from the delivery, rather than counted as modules pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's `intro n; exact etale_hypercover_product_data ... n` moved the entire
hypercover condition into one new sorry with an extra degree argument. It was a restatement,
not a strict component of the argument, and its node also cited the item in `stmt_deps`.
It is removed. Its docstring did not provide a complete construction or proof.

Chosen limits do need comparison maps, but Mathlib already provides the necessary APIs:
`isLimitOfHasBinaryProductOfPreservesLimit`, `mapIsLimitOfPreservesOfIsLimit`, and
`Over.isPullback_of_binaryFan_isLimit`. This avoids another transport placeholder.
Searches included `msearch.py ... loogle 'CategoryTheory.Limits.prod.map'`, and direct `rg`
searches for product preservation, surjectivity, `pullbackMap`, `isoPullback`, and matching
objects in Mathlib, `lean/Sheaf` and `lean/WeilConjectures`. The source files of the product
and pullback APIs and the existing matching-object theorem were read.

The cited local Stacks source is absent on this machine. The second reader read the
published [01GI](https://stacks.math.columbia.edu/tag/01GI) and
[01GH](https://stacks.math.columbia.edu/tag/01GH): the direct matching-object construction
and base-change/composition argument follow their route. No mathematical source correction
or statement change is needed. `coord/delivery-errors.md` currently has no section I.

## Second reading by J3

1. **Interface: pass after repair.** Compared the complete final module with the repository
   using `diff -u` and checked the declaration text up to `:=` byte for byte. The scheme,
   universes, qcqs instances, simplicial objects, both hypercover hypotheses and conclusion
   are identical. The original docstring, both public imports and visibility are retained.
   No definitions, existing auxiliary statements or other claimed modules are changed.
   The first worker's unnecessary public-import change record has been removed.
2. **Proof: pass.** The final file compiles through `lcompile.py`, without errors or warnings.
   It has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by` or `extern`. The explicit
   axiom check returns only `propext`, `Classical.choice`, `Quot.sound`. The chosen matching
   object is an actual categorical product of the objects from the hypotheses; no object
   is selected from an unproved existence theorem. Both projection equations identify
   the matching map with `eW.hom ≫ f ≫ eM.inv`, and Mathlib supplies surjectivity of `f`.
3. **Split statements: rejected and removed.** The proposed per-degree helper expands
   exactly one instance of the target's defining universal quantifier; it leaves all the
   argument in a new hole and is refused on reading even if a superficial tactic check
   might accept it. Replaced it with the full construction, so there are no split statements,
   new nodes or new holes to validate. Checked degree zero: the lower-simplex conditions
   are empty, the universal properties make both matching objects terminal over X, and
   their product is terminal; the same proof works. Degree one gives pairs of vertices
   and their product universal property. Empty X and empty lower-simplex diagrams require
   no nonemptiness hypothesis. The qcqs hypotheses remain unchanged and are not needed
   by this categorical argument.
4. **Route and pruning: pass after repair.** The proof constructs matching data top down
   from `hU n` and `hV n` and uses proved Mathlib statements for comparison and surjectivity.
   No imported sorry is needed. Read `dag/units/sk-prop-h2.json`: its `realized.statement`
   and sole `realized.steps` entry are empty; no fixed realization is bypassed. The
   hypercover-product step used by refinement remains the same theorem. All four removed
   old `proof_deps` and both removed imports are listed above. The added proof import
   is plain `import`; both original public imports are retained. Trial removal confirmed
   that additional site/pullback imports and elaboration options were unnecessary.
5. **Metadata: pass after repair.** Rebuilt the existing node's `proof`, `proof_deps` and
   `proof_origin` around the explicit Lean construction. Checked that `proof_deps` is
   exactly the union of `uses`; every other existing-node field equals the repository
   version. Removed the unlanded restatement node and module. There are no new nodes
   or change records in the final delivery.

Changes made during this reading: replaced the restatement by a complete proof; removed
its helper, node and change record; restored the original docstring and public imports;
minimized proof imports; restored the original open command by qualifying `Opposite.op`;
corrected proof metadata and the net-hole/pruning report.

The first dry run required a change record for adding `Opposite` to the module open
command. Restored that command exactly and qualified `Opposite.op` in the proof instead;
no interface change or change record is needed.
