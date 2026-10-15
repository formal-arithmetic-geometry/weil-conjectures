## What changed

Proved `CategoryTheory.ext_one_extension_classification` in
`Sheaf.CategoryTheory.ExtOneExtensionClassification` with its signature unchanged.
The proof constructs a triangle with prescribed boundary, proves its middle object
is concentrated in degree zero, lifts the arrows through the fully faithful single
functor, and uses Mathlib kernel/cokernel universal properties for short exactness.
A proved private helper establishes uniqueness of a single-triangle boundary from
TR3, Hom exactness and standard t-structure orthogonality. Equal classes then give
a middle-object isomorphism by TR3 and the two-isomorphisms criterion; the converse
is `extClass_naturality`. The exact-functor clause uses
`Abelian.Ext.mapExactFunctor_extClass` directly.

All dependencies are Mathlib. The private helpers are
`single_shift_negative_zero`, `shortExact_of_single_triangle`, and
`single_triangle_boundary_unique`. Added proof imports:
`Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory` and
`Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`.
The node proof, proof dependencies and proof origin now describe this argument.
The fixed proper-base-change unit route is unchanged; this is its downstream
categorical tool, not a realized unit step.

Change record: `coord/changes/C2-ext-one-classification-unused-import.md`.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ext_one_extension_classification`
(node `lem-weil-pbc-ext-one-extension-classification`). All three clauses are proved.
Added holes: none. Sorries left in the item or added modules: none.
This is a proof, not a decomposition.

The module compiles cleanly. `#print axioms` of the classification theorem reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed imports:

- `WeilConjectures.DeligneLaumon.Reduction.FormalSteps`: no source-library module
  is needed by this proof. Its entire otherwise-unneeded closure is avoided here.
- `Mathlib.Algebra.Homology.ExactSequence`: unused public finite-sequence API;
  the change record documents the import cleanup.
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`: redundant direct
  import, already available through the retained public `Ext.Map` import.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: redundant direct import,
  already available through `Ext.Map` and the retained `DerivedCategory.TStructure`.

The full abstract-heart node `lem-weil-heart-short-exact-triangles` is no longer a
proof dependency. Only its relevant kernel/cokernel and boundary-uniqueness facts
are needed; these are proved locally from existing Mathlib tools. Added the
existing Mathlib leaves `lem-weil-pbc-hom-into-triangle-exact` and
`lem-weil-pbc-hom-out-of-triangle-exact` to the actual proof dependency list.
The other original mathematical dependencies remain, with their Mathlib
implementations used directly. No module or node is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The `lean` record of `lem-weil-heart-short-exact-triangles` points to
`AlgebraicGeometry.WeilSheaf.exact_map_higherLowerShriek` in `FormalSteps`, which
does not state the general heart theorem used by the plan. This mismatch was
already noted in the stage-2 review. It is not an obstacle: Mathlib supplies the
needed generic kernel/cokernel lemmas, and the short boundary-uniqueness argument
is proved in this item. The mathematical classification statement is unchanged.
No enough-injectives/projectives assumption, boundedness assumption, or universe
restriction has been added.

## Second reading by C2

1. **Interfaces: PASS.** Compared the sole delivered module with the repository
   version. The complete existing theorem signature is byte-for-byte identical,
   including universes, hypotheses and all three conclusions; its docstring is
   unchanged. The only new declarations are three private proved helpers. There
   are no new or changed definitions. The removed public `ExactSequence` import
   is explicitly covered by the change record. Re-ran `tools/downstream.py` and
   confirmed its eleven-module list; compiled the unchanged sole direct importer,
   `Sheaf.Paper.CondensedFinitePresentationDescent`, against the delivered module
   in an isolated scratch sandbox. Both files compiled without errors or warnings.

2. **Proof and axioms: PASS.** Independently compiled the delivered module through
   `lcompile.py` without errors or warnings. Compiled a matching scratch copy with
   `#print axioms CategoryTheory.ext_one_extension_classification`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry` or forbidden
   declaration construct. Read all three private proofs and the main proof: the
   prescribed connecting arrow is retained when transporting the triangle;
   orthogonality kills the ambiguity in its boundary; and the lifted middle
   isomorphism has the two required endpoint equations. Choices occur only in
   the proof of an existential proposition and use proved Mathlib existence
   results, not unproved data specifications.

3. **Split statements: PASS, none.** No statements or holes are split off. The
   private helpers are fully proved. Checked their shifts and zero-object edge
   cases: negative-shift vanishing requires strictly negative degree, and the
   boundary argument uses the valid orthogonality bounds -1 and 0. The proof
   also applies to the zero class and split extensions without an extra
   hypothesis. Independent LeanFinder, Loogle and grep searches, together with
   searches in `lean/Sheaf` and `lean/WeilConjectures`, found no omitted direct
   classification or boundary-uniqueness theorem to replace the argument.

4. **Route and pruning: PASS.** Read the proof from its three conclusions down
   to the Mathlib declarations it uses. The exact-functor clause already uses
   the direct Mathlib theorem; the other clauses use triangle completion,
   standard-heart concentration, full faithfulness, kernel/cokernel universal
   properties and naturality. Each remaining proof import provides declarations
   used here. All four removed imports and the sole removed old proof dependency,
   `lem-weil-heart-short-exact-triangles`, are listed under `No longer needed`.
   Read `dag/units/sk-thm-properbasechange.json`: this categorical tool is not a
   realized statement or step of that unit, and none of its three steps is
   bypassed or changed.

5. **DAG: PASS.** Compared the delivered node with the original: only `proof`,
   `proof_deps` and `proof_origin` differ. Checked the referenced dependency
   records against the Mathlib uses in the Lean proof. `proof_deps` is exactly
   the union of the proof steps' `uses`, and the origin describes the argument
   actually implemented. No new nodes need validation.

Second-reading changes: appended this independent review and recorded additional
searches. No changes to the Lean proof, imports, node, or change record were needed.
