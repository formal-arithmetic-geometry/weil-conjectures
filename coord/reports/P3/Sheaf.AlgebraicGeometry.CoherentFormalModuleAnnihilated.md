## What changed

Closed `LinearMap.ker_coker_reduction_annihilated_double` using
`LinearMap.ker_coker_annihilated_mod_ideal`. Reduced
`AlgebraicGeometry.coherentFormalModule_annihilated_double` to two strictly smaller
component theorems, in new modules `Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleKernel`
and `Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleCokernel`.

## Proved and sorry left

The commutative algebra theorem `LinearMap.ker_coker_reduction_annihilated_double` is proved.
The parent affine-cover theorem is proved by conjunction of the two component declarations.
The original `AlgebraicGeometry.coherentFormalModule_annihilated_iff` remains sorry.
The new component declarations remain sorry:
`AlgebraicGeometry.coherentFormalModule_annihilated_double_kernel` and
`AlgebraicGeometry.coherentFormalModule_annihilated_double_cokernel`, with nodes of the same
suffixes. This is a strict decomposition into kernel and cokernel conclusions.

## No longer needed

No planned imports were removed. The parent node proof dependencies are now the two component
nodes. The original commutative algebra dependency is still used by the component proof plans.

## Where the brief, the DAG or earlier work was wrong

The parent theorem's proof plan omitted a Lean-level decomposition. The two new statements
make the independent kernel and cokernel obligations explicit; their conjunction is proved in
Lean and compiles.

## New nodes

`lem-weil-pbc-formal-systems-annihilated-by-power-kernel` and
`lem-weil-pbc-formal-systems-annihilated-by-power-cokernel` record the two component obligations.

## Second reading by P3

1. Compared the delivered parent module with the repository version. The existing theorem
   statements and definitions are byte-for-byte unchanged; the only existing proof change is
   the body of `coherentFormalModule_annihilated_double`, which now applies the two component
   declarations. The two component modules and their node files are new.
2. Compiled all three modules with `lcompile.py --all`. They compile without errors. There are
   no axioms, unsafe declarations, or hollow definitions. The original equivalence theorem
   remains the one explicitly listed sorry; the two component theorem sorries are named and
   documented in their module docstrings and nodes.
3. Checked the split statements against the parent type: each has exactly the same hypotheses
   and exponent as the parent and concludes one conjunct, so both are true obligations and are
   strictly simpler than the parent conjunction. Searches found no existing declarations with
   either component name or statement.
4. Checked the downward proof route. The parent uses both component nodes, and each component
   node retains the original commutative-algebra dependency and the same Remark 0888 source.
   No planned import or proof dependency was removed; the unit route remains represented by
   the parent node and its affine reduction dependency.
5. Checked DAG/Lean agreement: declaration names and signatures match the node records, the
   parent proof dependencies are exactly the two component nodes, and each new node records
   its source, proof plan, searches, unit, chapter, and split status.

The second reading found no mathematical or interface defect. I changed only this report
section and retained the compiled proof/decomposition described above.
