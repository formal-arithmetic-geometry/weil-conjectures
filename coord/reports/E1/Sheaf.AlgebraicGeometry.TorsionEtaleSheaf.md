## What changed

Replaced all three sorry proofs in
`lean/Sheaf/AlgebraicGeometry/TorsionEtaleSheaf.lean` with direct Mathlib arguments.
No signatures, definitions, public imports, or DAG route changed.

For `torsionKernelTransition_condition`, write `m.val = n.val * r` using divisibility.
Mathlib's `mul_nsmul` expresses multiplication by m as r copies of multiplication by n.
`Preadditive.comp_nsmul` moves that outer scalar past the kernel inclusion;
`kernel.condition` and `nsmul_zero` then give zero.

For `torsionKernelTransition_id`, cancel the monomorphism `kernel.ι (n.val • 𝟙 F)`.
Both sides become that inclusion by `kernel.lift_ι` and `Category.id_comp`.
For `torsionKernelTransition_comp`, cancel `kernel.ι (k.val • 𝟙 F)`.
Associativity and two applications of `kernel.lift_ι` reduce both sides to
`kernel.ι (n.val • 𝟙 F)`.
These are the elementary inclusion and compatibility arguments already recorded in
`def-weil-pbc-torsion-etale-sheaf`, preserving the definition realized by unit `sk-def-pbc`.

Searches: Loogle for `CategoryTheory.Limits.kernel.lift` found `kernel.lift_ι`;
LeanFinder for divisibility and kernels of integer multiplication returned general
kernel infrastructure but no exact theorem; launcher grep and local rg found
`Preadditive.comp_nsmul`, `kernel.condition`, and existing similar nsmul computations.
The relevant Mathlib signatures were read in `Preadditive/Basic.lean` and
`Limits/Shapes/Kernels.lean`. The module compiles cleanly with the prescribed launcher.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.torsionKernelTransition_condition`,
`AlgebraicGeometry.Scheme.torsionKernelTransition_id`, and
`AlgebraicGeometry.Scheme.torsionKernelTransition_comp` (all associated with node
`def-weil-pbc-torsion-etale-sheaf`). No sorry remains in this module; none added elsewhere.

## No longer needed

None. No proof imports were added, and the existing public imports were retained.
No dependency nodes or modules are pruned: the node had no proof dependencies and
its statement dependencies continue to describe the unchanged definition.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. This item consists of elementary kernel compatibility
proofs, so all three close directly from Mathlib without additional intermediate theory.
The blueprint source path recorded in the node is absent from this machine;
the unit record contains its statement and realized declarations, which were read.

## Second reading by E1

1. PASS: compared the entire delivered module with the repository using `diff -u`.
   Exactly the three existing theorem proof bodies change. All declaration signatures,
   definitions, docstrings, and public imports are byte for byte unchanged. There are
   no added declarations, adapted modules, or statement changes requiring a change record.
2. PASS: independently compiled the module with the prescribed `lcompile.py`, without
   errors or warnings. Read each proof: divisibility and `mul_nsmul` reduce the kernel
   condition to `kernel.condition`; cancellation of the monic kernel inclusions and
   `kernel.lift_ι` prove identity and composition. A scratch copy printing axioms of all
   three theorems and `IsTorsionAbelianSheaf` shows exactly `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`. No sorry, forbidden declaration, or hollow
   definition occurs in the module.
3. PASS: no statements were split off and no new nodes are needed. Checked the boundary
   cases conceptually: n = m uses the kernel condition, n = 1 gives the kernel of the
   identity, and repeated indices in composition reduce to the identity law. The proofs
   do not require extra positivity or nonzero hypotheses. Independent `rg` searches for
   kernel lifts and scalar composition in both Lean roots, and reading Mathlib's kernel
   and preadditive declarations, confirm that the existing short Mathlib route is enough.
4. PASS: the proof uses only the direct scalar and universal-property arguments; no
   heavier upstream theorem or extra proof import improves this route. The public imports
   supply the small etale sheaf category and its abelian/kernel infrastructure used in
   statements and the definition; none is a newly exposed proof-only import. The old
   `proof_deps` is empty, so `## No longer needed` is complete. Unit `sk-def-pbc` still
   realizes its statement through this node; its steps are empty and its colimit-based
   torsion definition is preserved verbatim.
5. PASS: read `def-weil-pbc-torsion-etale-sheaf.json` and `sk-def-pbc.json`. This is a
   definition node, with empty `proof`, `proof_deps`, and null `proof_origin`; the elementary
   inclusion and compatibility claims are spelled out in its statement and split report.
   The unchanged definition implements them with these now-proved auxiliary theorems,
   so no DAG field needs alteration and no new-node schema applies.

Second reading changed only this report: no Lean repair was needed.
