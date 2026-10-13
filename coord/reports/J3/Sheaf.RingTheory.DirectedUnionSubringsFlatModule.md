## What changed

Proved `RingTheory.directedUnionSubrings_flat_module` in
`Sheaf.RingTheory.DirectedUnionSubringsFlatModule` using Mathlib's equational criterion
(`Module.Flat.of_forall_isTrivialRelation` and
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`). Descend the finitely many coefficients
and module representatives to one common stage; use `h_zero` on the sum of the relation
to obtain a genuine zero relation at a later stage; trivialize it by stage flatness;
map its matrix and module elements back to the original ring and module.

Replaced the proof-only tensor-colimit import with proof-only imports of
`Mathlib.RingTheory.Flat.EquationalCriterion` and `Mathlib.Data.Finset.Order`.
Updated only `proof`, `proof_deps`, and `proof_origin` of the existing DAG node to
record the actual route, and updated the declaration's proof docstring.
The existing declaration signature and its visibility are unchanged. A declaration-scoped
unused-variable linter option preserves the original unused bound `i` in
`Mstage : ∀ i : Λ, Type x` without a compiler warning. The proof explicitly clears
`t_id` and `t_comp`: the stronger pointwise criterion needs naturality and eventual
vanishing but not these two compatibility assumptions.

## Proved and sorry left

Closed the only original hole:
`RingTheory.directedUnionSubrings_flat_module`
(node `lem-weil-pbc-directed-union-subrings-flat-module`).
Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module, and no
new module or holed dependency was added. This is a proof, not a decomposition.

Single-file compilation succeeds. Edge cases covered by the proof include the empty
finite relation (the common upper bound exists by nonemptiness), the zero ring and
zero module, arbitrary index and module universes, and noninjective transition maps
(the relation is killed by `h_zero`, never by an assumed injective coprojection).
The additive-group structures are constructed from the existing module structures
using `Module.addCommMonoidToAddCommGroup`; no structure is chosen from an unproved theorem.

## No longer needed

Removed proof-only import:
`Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`.

Removed proof dependencies from this node:
- `lem-weil-pbc-flat-fg-ideal-criterion`;
- `def-weil-pbc-category-colimit`;
- `lem-weil-pbc-filtered-colimit-tensor-varying-rings`;
- `def-weil-pbc-flat-ring-map` (still retained as the statement's definition dependency);
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`.

In particular the varying-ring tensor comparison module is no longer reached through
this module. No categorical colimit construction, cofinal upper-set construction,
ideal descent, or filtered-colimit exactness is required by this proof. Whether their
modules leave the entire targets' closure depends on other importers. The only new
proof dependency is the existing Mathlib leaf `lem-weil-pbc-flat-equational-criterion`.
No node realizing the unit's statement or proof steps is bypassed: the item is below
those unit realizations in `dag/units/sk-thm-p1.json`.

## Where the brief, the DAG or earlier work was wrong

The original ideal/tensor-colimit proof plan is mathematically valid but unnecessarily
large for the available interfaces. Mathlib already supplies both directions of the
equational criterion. The same shorter route is already used for the nearby
`RingHom.flat_of_flat_comp_colimit_ι`; here the additional `h_zero` hypothesis kills
the lifted relation before applying stage flatness. No statement correction, forced
adaptation, new node, or target change is needed.

## Second reading by J3

1. Compared the delivered Lean module with the repository version. The theorem signature and
   visibility are byte-for-byte unchanged; only proof text, proof-only imports, and declaration
   documentation changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it is error- and sorry-free. The proof uses only the
   equational criterion and existing hypotheses; no axioms, unsafe declarations, or hollow
   definitions were introduced. Verdict: pass.
3. Checked the route against Mathlib and the repository. The finite-relation argument is a
   genuine reduction, and the DAG node records the criterion dependency and updated proof
   origin. No new statement or duplicate library result was added. Verdict: pass.
4. The equational proof removes the tensor/colimit route and its unused imports and dependency
   nodes; the report lists each removed item. The unit's realized route remains unchanged.
   Verdict: pass.
5. The DAG proof, proof dependencies, and proof origin match the Lean proof, and the existing
   node metadata and statement remain unchanged. Verdict: pass.

Changed after reading: no repairs were necessary; only this second-reading record was added.
