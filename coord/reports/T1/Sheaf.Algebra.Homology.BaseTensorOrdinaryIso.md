## What changed

Added the proof import `Sheaf.Algebra.Homology.BaseTensorOrdinaryDegreeIso` and proved
`ModuleCat.exists_baseTensorOrdinaryIso` by choosing the degreewise tensor comparison and
assembling it with `HomologicalComplex.Hom.isoOfComponents`. The differential compatibility
proof reduces on pure tensors to the generator formula and A-linearity of the differential.
Added the intermediate degreewise theorem module and its DAG node.

## Proved and sorry left

Closed the hole in `ModuleCat.exists_baseTensorOrdinaryIso` by a compiling reduction. This is a decomposition, not a net proof: one hole closed and one hole added. The new intermediate declaration
`ModuleCat.exists_baseTensorOrdinaryDegreeIso` remains `sorry`; it is strictly the degreewise
isomorphism and generator formula used by the complex assembly.

## No longer needed

The original module imports only the stated Mathlib modules plus the new degreewise module.
No existing imports, nodes or modules are pruned: the two original definition dependencies remain needed by the degreewise intermediate theorem.

## Where the brief, the DAG or earlier work was wrong

The imported plan omitted the substantial scalar-action transport needed to apply
`Algebra.IsPushout.cancelBaseChange` to `ModuleCat`'s ring-hom-based extension and restriction
functors. This was isolated as the degreewise intermediate theorem.

## New nodes

`lem-pc-base-tensor-ordinary-degree-iso` records the degreewise comparison theorem left for a
parallel worker.

Dry run: both modules compile cleanly and deliver3.py prints OK; the second reading
is deferred to the second reader. No files were pushed.

## Second reading by T1

1. Compared `BaseTensorOrdinaryIso.lean` with the repository version. The existing
   declaration signature is unchanged; only its proof and the declared proof import
   were added. The new degreewise module and node are included explicitly.
2. Compiled both delivered modules with `lcompile.py`. There are no errors, forbidden
   declarations, or `sorry` inside a definition. The only remaining proof hole is the
   named `ModuleCat.exists_baseTensorOrdinaryDegreeIso` theorem, whose node and
   docstring record the decomposition. The target theorem depends on `sorryAx` only
   through that named intermediate theorem.
3. Checked the degreewise statement against its node and the source construction.
   It is the required B-linear tensor comparison with the stated pure-tensor formula,
   with no added hypotheses or weakened conclusion. The intermediate theorem is
   strictly simpler than the complex theorem and is needed by its proof.
4. The complex proof follows the unit route: degreewise comparison, differential
   compatibility by tensor induction and A-linearity, then
   `HomologicalComplex.Hom.isoOfComponents`. The imports are minimal for the
   declarations used; the degreewise theorem's two public Mathlib imports support
   its statement.
5. The DAG proof and `proof_deps` agree with the Lean proof: the complex node now
   depends on the degreewise node, and the new node records its own dependencies,
   source, Lean declaration, and split status. No old dependency is pruned.

Changed only the report during this second reading; no Lean statements or proofs
needed repair.
