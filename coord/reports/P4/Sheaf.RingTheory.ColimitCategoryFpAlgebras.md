## What changed

Proved `RingHom.exists_map_of_finitePresentation_colimit` in
`Sheaf.RingTheory.ColimitCategoryFpAlgebras`, preserving its signature and visibility.
A proved private helper `RingHom.exists_tensorStage_factorization` descends a map from
`A` by descending finitely many polynomial generators and finitely many kernel relations.
The original theorem extends that map by the tensor universal property and proves the
commuting square by tensor induction. Equality descent is proved using finite algebra
generators and the existing, proved elementwise tensor colimit theorem.

The second reading removed the redundant added proof-only imports
`Mathlib.Data.Finset.Order` and `Mathlib.RingTheory.Ideal.Quotient.Operations`:
both are already available through the original public imports. Kept the existing import
`Sheaf.Paper.DirectedColimitBaseChangeElementwise`. Updated the existing DAG node's
proof, proof_deps and proof_origin to this direct finite-presentation argument.
The original docstring's categorical-colimit argument remains a valid alternative;
the DAG now records the implemented proof.

## Proved and sorry left

Closed the sole original hole: `RingHom.exists_map_of_finitePresentation_colimit`
(node `lem-weil-pbc-colimit-category-fp-algebras`). The private factorization helper
is also completely proved. No `sorry` remains, no holes were added, and no statements
were split off. The imported elementwise theorem is already proved.

The whole delivered module compiles with no warnings through `lcompile.py`.
The construction covers empty generator and relation sets using the nonempty upper
tail; its proof does not require finite presentation of `A'`, although the original
public theorem retains that hypothesis unchanged. No definition or target was changed.

## No longer needed

Removed no original imports. Removed the first worker’s redundant added imports
`Mathlib.Data.Finset.Order` and `Mathlib.RingTheory.Ideal.Quotient.Operations` during
second reading; no new import is needed. These modules remain transitively available,
so this does not prune a module from the import closure. The temporary factorization
module was folded into a proved private helper and is not part of the delivery.

The proof no longer needs these former proof dependencies:
- `lem-weil-pbc-filtered-colimit-algebras-elementwise` (Mathlib leaf; no Sheaf module).
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`
  (Mathlib leaf `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`).
- `lem-weil-pbc-algebra-tensor-base-change-universal-property`
  (Mathlib leaf `AlgHom.liftEquiv`; the tensor pushout lift supplies the extension).

No library modules were removed from the actual import closure. These three DAG
proof edges are pruned only for this theorem; their other users are unaffected.
The node is not a realization of a unit statement or proof step, and the unit route
is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The original DAG's categorical identification
of the tensor target as a colimit is unnecessary: the proved elementwise theorem
already supplies both representation and eventual vanishing, allowing the finite
presentation argument to be implemented directly with arbitrary source/target universes.
No forced adaptations, new public statements, or new nodes are needed.


## Second reading by P4

1. **Unchanged interfaces — PASS.** Compared the entire module with the repository
   using `diff -u`, and mechanically checked that the existing theorem signature is
   byte-for-byte identical. Its hypotheses, universe parameters, visibility, and both
   conclusions remain unchanged. No public definition or statement was added or
   altered; there are no change records or forced adaptations. The only added
   declaration is a completely proved private helper.
2. **Proof and axioms — PASS.** Compiled the module through `lcompile.py`, with no
   warnings or errors. A scratch copy containing `#print axioms` for both
   `RingHom.exists_tensorStage_factorization` and
   `RingHom.exists_map_of_finitePresentation_colimit` compiled after removing both
   redundant imports. Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`;
   neither uses `sorryAx`. Scanned the delivered Lean for sorry, axiom, unsafe, opaque,
   implemented_by, extern, and kernel-check bypasses: none. All choices and quotient
   lifts use proved existence or surjectivity facts, not unproved witness theorems.
3. **Split statements — PASS (none).** No holes were split off, no new nodes were
   introduced, and the helper is proved rather than a restatement with a hole. Read
   its generator descent, relation descent, kernel inclusion, and quotient lift.
   Empty variable and relation sets are covered by `Nonempty J` and
   `Finset.exists_le`; the equality clause also handles an empty algebra-generating
   set by including the original index in a common upper bound. Nothing requires
   injective transition maps, antisymmetry, or finite presentation of the target
   algebra. Independent searches using `msearch.py` (leanfinder, loogle, grep) and
   `rg` on the upstream and Sheaf libraries found no ready-made theorem replacing
   this right-tensor descent proof. Mathlib's categorical finite-presentation lemmas
   require constructing the tensor algebra colimit, and have a common ring universe;
   they do not supply a shorter direct application to this signature.
4. **Route and pruning — PASS.** Read the proof from the public theorem down to the
   helper and the already-proved elementwise theorem. Checked the argument against
   [Stacks 05N8](https://stacks.math.columbia.edu/tag/05N8), parts (1) and (3), and
   [Stacks 05N9](https://stacks.math.columbia.edu/tag/05N9), parts (2) and (3).
   The three former proof dependencies absent from the new proof are all listed
   under `## No longer needed`. No original import was removed; the new imports
   were redundant and have now been removed. Inspected `dag/units/sk-thm-p1.json`:
   this item is absent from its `realized.statement` and every `realized.steps`
   entry, so the alternative node-level proof preserves the unit route.
5. **DAG agreement — PASS.** Diffed the node: only `proof`, `proof_deps`, and
   `proof_origin` differ. The four proof steps match the helper and the two public
   clauses. `proof_deps` is exactly the union of the steps' `uses`, retaining the
   elementwise tensor theorem, finite-presentation and colimit definitions, and
   tensor pushout tool. No new-node fields are needed.

Second-reading changes: removed the two redundant proof imports, clarified in an
inline proof comment that the implemented argument is the direct finite-generator
and finite-relation route (the existing docstring records a valid alternative),
and corrected this report's import account. The proof terms needed no repair.
Closed holes: `RingHom.exists_map_of_finitePresentation_colimit` (1 of 1 original).
Added holes: none. Split off: none. Library modules pruned: none; three former
DAG proof edges are pruned as listed above.
