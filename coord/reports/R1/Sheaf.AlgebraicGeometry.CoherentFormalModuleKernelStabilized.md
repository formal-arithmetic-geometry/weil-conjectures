## What changed

Replaced the proof hole in `coherentFormalModule_kernel_stabilized_aux` by combining two strictly smaller intermediate statements: a uniform stabilization bound and construction of a compatible stabilized system. Added the corresponding modules and DAG nodes.

## Proved and sorry left

`coherentFormalModule_kernel_stabilized_aux` is proved by the real Lean combination of the two intermediate declarations. The new declarations `coherentFormalModule_kernel_stabilized_bound` and `coherentFormalModule_kernel_stabilized_system` remain `sorry`, each with its own node.

## No longer needed

The original affine, Artin--Rees, kernel, and ideal-product imports are not used directly by the combining proof and were pruned from the item module.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the affine Artin--Rees bound and compatible-system construction into one unproved statement; they are split into two strictly smaller statements to make the dependency reduction explicit.

## New nodes

`new-kernel-stabilized-bound` and `new-kernel-stabilized-system` are the two intermediate theorem nodes stated in the new modules.

## Earlier second reading (a previous round; superseded)

The combining proof preserves the original target statement exactly. The two new statements are strict components: the first supplies only the common bound, and the second supplies only the compatible system from that bound. The unit route through stabilization is retained.

## Second reading by R1

1. Compared the delivered item module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and the proof body changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The target proof compiles; the only remaining `sorry`s are the two named split-off theorems, each with a matching node, and no prohibited declarations or hollow definitions were introduced. Verdict: pass.
3. Checked both split-off statements against the stabilized-kernel argument and searched the library for existing declarations. The bound and compatible-system statements are true strict components, have source/docstrings, and are not duplicates. Verdict: pass.
4. Reviewed the proof route and imports. The target combines the bound and system in the stated unit route; unused legacy imports were removed from the item module. Verdict: pass.
5. Checked DAG agreement: the item proof uses exactly `new-kernel-stabilized-bound` and `new-kernel-stabilized-system`, and both node `lean` records match their declarations. Verdict: pass.

Changed during second reading: removed the unused legacy imports from the item module and added this review record.
