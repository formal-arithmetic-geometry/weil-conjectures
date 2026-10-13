## What changed

The delivered module is the existing complete proof, with only a proof-term
normalization in `exists_presheaf_ext_local_killing`: the existing witness theorem
is invoked through `simpa only [] using`. No declaration signature, definition,
visibility, import, or node statement changed.

## Proved and sorry left

`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing` are both fully proved.
There are no `sorry` declarations in the delivered module and no new split-off
statements. This delivery verifies an already landed proof and closes zero new
holes.

## No longer needed

None. The existing imports and proof dependency edges are used by the complete
witness construction and its wrapper theorem; no imports, nodes, or modules are
pruned.

## Where the brief, the DAG or earlier work was wrong

The item was already complete in the repository before this worker started:
its proof and the prerequisite `Ext.exists_epi_comp_eq_zero` had already landed.
The brief's stale description of an open item therefore does not match the
current repository state. No mathematical or interface error was found.

## New nodes

None.

## Second reading by H4

1. **Repository comparison.** I compared the delivered module with the repository version. The two theorem signatures, private helper interfaces, definitions, visibility, and imports are byte-for-byte unchanged; the only difference is the final proof term (`simpa only [] using` in the delivery versus `exact` in the repository).

2. **Proof and axioms.** The module compiles with `lcompile.py`, with no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Scratch `#print axioms` for both public theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and split-offs.** No statement was split off and no new node was added. The existing witness and wrapper statements are unchanged, and the wrapper is proved directly from the witness theorem. A search of the repository found no duplicate declaration or stronger/weaker replacement introduced by this delivery.

4. **Route and pruning.** The proof follows the existing unit route: the witness theorem uses the Ext epi-effacement result and the local-cover construction, while the wrapper applies the witness theorem. The imports and proof-dependency edges remain needed; no pruning was identified. The `simpa only []` normalization is proof-only and does not alter the route.

5. **DAG agreement.** The two existing DAG nodes have proof steps and `proof_deps` matching the declarations and proof. Their statements and unit realization remain unchanged.

I changed nothing after this second reading; the delivered proof-only normalization is compilable and axiom-clean.
