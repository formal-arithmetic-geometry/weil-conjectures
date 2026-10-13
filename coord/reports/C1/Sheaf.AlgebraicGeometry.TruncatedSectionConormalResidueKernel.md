## What changed
Added the structural submodule form `truncated_section_conormal_residue_kernel_comap` and reduced the original theorem to it. The original theorem is now proved by applying the comap inclusion.

## Proved and sorry left
`truncated_section_conormal_residue_kernel` is closed. `truncated_section_conormal_residue_kernel_comap` remains a sorry, recorded by node `lem-weil-pbc-truncated-section-conormal-residue-kernel-comap`.

## No longer needed
Removed proof-only imports `Mathlib.RingTheory.Smooth.Kaehler` and `Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`; the open split theorem has no proof body that uses them.

## Where the brief, the DAG or earlier work was wrong
The DAG did not contain the structural comap intermediate required to state the hard residue-quotient argument as a separate theorem.

## New nodes
`lem-weil-pbc-truncated-section-conormal-residue-kernel-comap` records the remaining structural inclusion.

## Earlier second reading (a previous round; superseded)
The structural inclusion is a strict submodule formulation used by the parent theorem; the remaining proof is exactly the Artin--Rees and square-zero argument recorded in its docstring and node.

## Second reading by C1

1. Compared the delivered module with the repository version. Existing theorem signatures are byte-for-byte unchanged; the only declaration added is the documented structural intermediate. Verdict: pass.
2. Compiled the module with `lcompile.py`; it is clean. The remaining `sorry` is only the named public theorem `truncated_section_conormal_residue_kernel_comap`, and it has a matching node and proof docstring. The closed parent theorem has no `sorry`. Verdict: pass.
3. Checked the split statement and searched the library and Mathlib for an existing declaration. No duplicate declaration was found. The comap form is the submodule interface consumed by the pointwise theorem. Verdict: pass.
4. Checked the proof route and imports. The parent theorem is reduced to the comap inclusion; the comap node now cites the underlying square-zero, base-change, differential, and mod-power ingredients rather than the parent theorem, avoiding a circular DAG dependency. Removed the two proof-only imports that are unused while the split theorem remains open. Verdict: pass.
5. Checked the new node fields, declaration attachment, source, blueprint link, and unit/chapter. The unit route remains `sk-thm-p1`; the node proof and `proof_deps` agree. Verdict: pass.

Changed in this second reading: removed unused proof-only imports and repaired the new node's proof dependency route to remove the circular parent dependency. No theorem statement or definition was changed.
