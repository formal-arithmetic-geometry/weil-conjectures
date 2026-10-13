## What changed
Reduced `RingHom.exists_comparison_tensor_cocones` to the construction of a tensor comparison system independent of the global map ζ. Added a proof-only import of `Sheaf.RingTheory.ComparisonTensorLocalSystem`. The new construction statement retains the canonical legs, transitions, pushout squares and left compatibility, and records the constant Q-coordinate in the target limit. The original theorem proves global compatibility by tensor ring-hom extensionality: he checks the B-factor, hlim checks the Q-factor. No existing signature changed.

## Proved and sorry left
Closed the direct hole in `RingHom.exists_comparison_tensor_cocones` by a decomposition, not an axiom-free proof of the full construction. Added one hole: `RingHom.exists_comparison_tensor_local_system`, node `lem-weil-pbc-comparison-tensor-local-system-j3`. The global compatibility argument is proved in Lean; the independent local construction is the remaining item.

## No longer needed
No imports or construction dependencies are pruned. The original module still needs its three public Mathlib imports for its signature. The original node's direct base-change universal-property dependency moves to the local construction node; tensor ring-hom extensionality remains a direct dependency.

## Where the brief, the DAG or earlier work was wrong
No mathematical error identified. The two stated universal-property nodes are Mathlib leaves, rather than ready-made indexed constructions. The nearby higher theorem `exists_comparison_map_base_change_system` depends on this module and cannot be used as a shortcut. The new statement was checked against terminal indexing, identity transitions, arbitrary Q, and zero rings: its construction uses no bijectivity, finite presentation or nontriviality. The P-actions are transported through the canonical transitions; their compatibility with the limit follows from the given P-linear μB.

## New nodes
`lem-weil-pbc-comparison-tensor-local-system-j3` in `Sheaf.RingTheory.ComparisonTensorLocalSystem` isolates construction of the system and its Q-coordinate, without a global comparison map or the hypotheses he/hlim. It follows steps 1 and 3 and the canonical-leg part of step 2 of the original plan. The original theorem supplies the missing global comparison by checking the two tensor inclusions. No change record is needed because the existing signature and public imports are unchanged.

## Second reading by J3

1. Compared the delivered cocones module with the repository version. Existing declaration signatures are unchanged byte for byte; the only interface addition is the proof-only import and the separately documented split node.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation is clean. The cocones target has no `sorry`, while the local-system theorem retains its explicitly named split `sorry`; no forbidden declarations or hollow definitions were introduced. Explicit `#print axioms` checks of both declarations returned exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, with the last coming from that open theorem.
3. Checked the split statement against terminal, identity-transition, zero-ring, and arbitrary-Q cases. It is a true strict reduction of the construction and does not restate the original theorem; its source, proof plan, declaration, and node agree.
4. Reviewed the proof route and imports. The cocones proof uses the local construction and tensor ring-hom extensionality for the global compatibility clause; all three public imports are needed by the statement, and the local-system import is proof-only. The unit route and realized steps are preserved; no additional pruning was found.
5. Verified DAG metadata and report consistency: the original node records the decomposition and the new local-system node records the remaining hole, source, dependencies, and declaration exactly.

Clarified the local-system docstring and its DAG proof step: the canonical limit map does not factor through B_i; instead its composite with B_i → B_j equals μB, which proves P-linearity for the transported P-action. No Lean proof or statement required repair. The global compatibility is a genuine reduction, but the delivery remains a decomposition (one hole closed, one added; net zero). Independent searches with leanfinder, loogle (ringHom_ext), and grep (cancelBaseChange/isPushout_tensorProduct), and searches of both library roots, found component lemmas rather than an existing complete indexed construction.
