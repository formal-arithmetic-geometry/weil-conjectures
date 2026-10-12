## What changed

Proved `AlgebraicGeometry.Scheme.FiniteEtale.fiber_equivalence_finiteEtale_baseChange`.
The proof combines `fundamentalGroupMap_injective` with
`fundamentalGroupMap_range_eq_stabilizer`, and derives finite index from the
finite nonempty geometric fibre using `Subgroup.finiteIndex_iff`.

## Proved and sorry left

The finite étale base-change theorem is proved. The declarations
`exists_fiber_flc_equivalence` and `fiber_equivalence_baseChange` remain `sorry`
(their existing nodes are `thm-galois-fundamental`).

## No longer needed

No imports or DAG dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The planned finite étale clause directly follows from the already stated image and
injectivity lemmas; no additional categorical construction is needed for this clause.


## Second reading by H1

1. Compared the complete delivered module against the repository with `diff -u`,
   and checked it with `stage3_delivery.diff_module`. All existing signatures are
   byte-for-byte unchanged. The only Lean change is replacement of the third
   theorem's proof. No definitions, declarations, or imports changed.
2. Compiled the delivered module through `lcompile.py`: exit code 0, no warnings.
   Compiled a scratch copy with `#print axioms` for all three theorems. Their only
   axioms are `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The third
   theorem still depends on the existing open image–stabilizer theorem; it is a
   proved reduction, not an axiom-free completion of the node. The two remaining
   local sorries are precisely the named theorems listed above, with their existing
   source/proof docstrings and node. No forbidden declarations or hollow definitions.
3. No new statements or split-off theorems were introduced. Checked the existing
   image–stabilizer statement used in the reduction, including the degree-one case.
   The geometric point supplies nonemptiness of X, so the finite fibre's cardinality
   is positive; the argument does not silently assume a nonempty arbitrary cover.
   Searched Mathlib's group theory for stabilizer finite-index alternatives and
   `finiteIndex_iff`, and searched the upstream/project fundamental-group modules.
   The existing injectivity theorem and image–stabilizer theorem are the direct route;
   no restatement of the item was added.
4. Reviewed the proof from its conclusion downward. Injectivity, range, and openness
   are projections of the stated dependencies; finite index follows from the index
   formula, finite nonempty fibre, and `Subgroup.finiteIndex_iff`. Public imports
   supply the signatures' sheaf/fundamental-group topology and subgroup-index notions;
   the proof's other imports are plain imports. Retained the plan imports for the
   two open clauses, so no dependency of the whole node can yet be pruned. Read
   `dag/units/sk-prop-h2.json`: its statement and realized route are unchanged.
5. Read `thm-galois-fundamental` and its proof/dependency/origin records together with
   the Lean and dependency modules. Step 5 already names injectivity, image–stabilizer,
   and geometric-fibre finiteness, exactly the ingredients used here; the other steps
   describe the two still-open clauses. No new nodes are required and no existing
   proof dependencies become unused by the complete node.

Second reading changed only this report: clarified the distinction between the one
locally closed proof and its remaining upstream `sorryAx` dependency. The Lean proof
and DAG were correct and were retained.
