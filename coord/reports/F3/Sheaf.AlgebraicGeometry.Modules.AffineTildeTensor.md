## What changed

Proved `AlgebraicGeometry.affine_tilde_tensor` with its original signature.
Constructed the R-bilinear pure-section tensor map and lifted it with `TensorProduct.lift`.
Used Mathlib's tilde adjunction to construct alpha and prove its uniqueness.
Added `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensorStalk`, proving the canonical
comparison bijective on each stalk by the existing stalk tensor isomorphism and Mathlib's
module localization equivalence. The main proof uses the stalk criterion and the tilde
unit isomorphism to finish isomorphy and global bijectivity.
Updated the parent proof plan to cite this proved intermediate lemma, keeping the same
Stacks 01I8(1) second-proof route and every unit realization unchanged.
All new proof imports are non-public; existing public imports and declarations are unchanged.

## Proved and sorry left

- Proved `AlgebraicGeometry.affine_tilde_tensor`
  (lem-weil-pbc-affine-tilde-tensor): the item's sole sorry is removed.
- Proved `AlgebraicGeometry.affine_tilde_tensor_stalk_bijective`
  (lem-weil-pbc-affine-tilde-tensor-stalk-bijective): no sorry added.
- No sorry remains in either delivered module. The proof uses the existing
  `SheafOfModules.stalkTensorIso` declaration from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor`, which remains an existing
  upstream proof obligation (lem-pc-ringed-space-module-stalk-tensor,
  also realizing lem-weil-pbc-module-stalk-tensor).

Both modules compile without warnings through lcompile.py. The zero ring case requires
no stalks; zero M or N is covered by the same localization statements. No finiteness,
nonzero-ring, domain or nonzero-module hypothesis is introduced.

## No longer needed

Removed direct proof imports of `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor` and
`Sheaf.Topology.PresheafModuleStalkFunctor` from the item, replacing them with the proved
stalk-comparison module. StalkTensor remains used in that module, and its transitive
module-stalk dependencies remain needed. The following old direct proof dependencies now occur only through the proved
intermediate node: `lem-weil-pbc-spec-domain-stalks-function-field`,
`def-weil-pbc-module-stalk`, `lem-weil-pbc-spec-tilde-stalk-localization`,
`lem-weil-pbc-localization-tensor-product`, and `lem-weil-pbc-module-stalk-tensor`.
No mathematical node or module of the original argument is pruned globally:
steps 3-5 now occur in the proved intermediate node.
The naturality clause of stalkTensorIso is unused; its pure-section germ formula suffices.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The global bilinear map requires converting
R scalar multiplication to multiplication by the corresponding global function; this is
handled by Scheme.Modules.smul_Spec_def. Mathlib's localization uniqueness theorem removes
the need to write a separate fraction injectivity/surjectivity argument.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and source searches
were performed and recorded. The local literature source is absent in this clone, so the
second proof and mapping property were checked against the official Stacks pages
https://stacks.math.columbia.edu/tag/01I8 and https://stacks.math.columbia.edu/tag/01I7.

## New nodes

`lem-weil-pbc-affine-tilde-tensor-stalk-bijective`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-tilde-tensor-stalk-bijective.json`,
records steps 3-5 of the original argument. Its theorem is proved, not a new sorry:
localize the module tensor, compare the canonical morphism on pure global germs, and use
uniqueness of module localization to obtain a bijection on each stalk. Its Lean module is
`Sheaf.AlgebraicGeometry.Modules.AffineTildeTensorStalk`. No change record is needed because
no existing statement, definition, or public import changes.


## Second reading by F3

1. Compared every delivered existing module and node with the read-only repository.
   The sole existing theorem signature is byte-for-byte identical, including every
   binder and conclusion; no existing definition or public import changed. Pass.
2. Compiled both modules in import order using lcompile.py, without errors or warnings.
   Searched both sources for sorry and forbidden declarations/options: none.
   Scratch copies with `#print axioms` for both theorems reported only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is an existing dependency
   through `SheafOfModules.stalkTensorIso`, whose source and germ formula were read.
   No new axiom or hole is introduced. Pass, conditional on that existing obligation.
3. The new stalk theorem is fully proved and is strictly the stalk comparison part of
   the argument, not a restatement of the item. Read the localization equivalence and
   tensor-localization instances in Mathlib. Its hypothesis identifies the canonical map
   on generating pure tensors; localization uniqueness then forces bijectivity. Zero
   modules satisfy the same argument and the zero ring has no primes. Repeated searches
   with different wording using LeanFinder, Loogle, msearch grep, and rg over project,
   upstream and Mathlib sources found no existing theorem replacing this comparison.
   The docstring gives the full argument and the new node records it. Pass.
4. Read the proof from beta's construction through the adjunction, stalk criterion and
   global-section bijectivity. Each import supplies statement vocabulary or a proof tool;
   new proof imports are plain imports. The argument follows the second proof of
   [Stacks 01I8](https://stacks.math.columbia.edu/tag/01I8) and the mapping property of
   [01I7](https://stacks.math.columbia.edu/tag/01I7). Reviewed sk-thm-p1's realized fields:
   none is bypassed or edited. Listed every removed old direct proof dependency under
   No longer needed; they remain used transitively, so global pruning is none. Pass.
5. Checked both node statements, proof steps, dependency unions, proof origins, and
   the new node's Lean signature and required fields against the code. The parent
   delegates precisely the localization/stalk steps to the new proved node. Pass.

Second reading changed only reporting and DAG cross-references: completed the list
of old direct dependencies moved to the helper and corrected the parent's obsolete
Step 5/Step 6 references to Step 3/Step 4. No Lean repair was necessary.
