## What changed

The existing target signature and docstring are unchanged. Its proof combines a limiting kernel fork, `ShortComplex.exact_of_f_is_kernel`, `mono_of_isLimit_fork`, and the quotient epimorphism with `ShortComplex.ShortExact.mk'`. The two new modules separate the kernel universal property from surjectivity. The second reader proved the quotient epimorphism directly using standard opens, local invertibility of twistMul, monoidal pullback, and stalk surjectivity.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exists_proj_coordinate_shortExact` (node `lem-sc-p1-proj-coordinate-short-exact`), conditionally on the kernel-fork lemma. Added one remaining hole: `AlgebraicGeometry.exists_proj_coordinate_kernel_fork` (node `lem-sc-p1-proj-coordinate-kernel-fork`). The new theorem `AlgebraicGeometry.proj_coordinate_quotient_epi` (node `lem-sc-p1-proj-coordinate-quotient-epi`) is fully proved; the second reader closed its initially proposed hole.

This is a decomposition of the original one hole into one strictly smaller kernel-universal-property hole, not a complete proof of the coordinate sequence. Net holes closed minus added: zero. No definition was added or modified, and no arbitrary existence witness is used as the data of a definition.

## No longer needed

The old direct proof dependencies `def-weil-pbc-proj-twisting-sheaf` and `lem-pc-twist-tensor` are replaced at the target node by the two new coordinate nodes. The twisting-sheaf definition remains used transitively. The remaining kernel calculation uses coordinate multiplication directly, so does not need twist tensor-addition. No existing module import was removed, and no whole module is claimed pruned. Removed redundant explicit imports of ProjectiveSpectrum.Basic and Modules.Sheaf from the quotient module (both are already exported by Twist). Removed the unused ShortExact import from both new modules; the kernel module imports Kernels instead. All added imports needed only by proofs are plain imports.

## Where the brief, the DAG or earlier work was wrong

The first delivery's new nodes depended circularly on the parent theorem, had placeholder statements and Lean records, and lacked search records. The split theorem docstrings did not include complete proofs. The target node still described the old route. These faults are repaired. The original report overstated the result as proved: the delivery is a decomposition. The categorical combination itself was correct, apart from a style warning fixed by replacing `letI` with `let`.

## New nodes

`lem-sc-p1-proj-coordinate-kernel-fork`: the remaining local kernel universal property with precisely G(z-1) as source, zero composite, and an IsLimit witness. Its docstring specifies the coordinate lift construction and the unique local factorization on each chart, then gluing. It has no proof dependency on the parent theorem.

`lem-sc-p1-proj-coordinate-quotient-epi`: the quotient epimorphism, now proved from existing local isomorphism, monoidal pullback, and stalk interfaces. No change record is required because no existing statement or definition changed.

## Second reading by D3

1. Compared the target module against the repository with diff: only two plain proof imports and its proof body changed. The existing theorem signature is byte-for-byte identical; no existing definition or target statement changed. The other two modules are new.
2. Compiled all three delivered modules using lcompile.py. There is exactly one sorry, the named kernel-fork theorem. No axiom declaration, unsafe, opaque, implemented_by, extern, or holed definition occurs. Separate scratch copies check all three declarations with #print axioms; results are recorded below. The choice of an IsLimit witness is local to a proposition proof, not the data of a definition.
3. Read both split statements as independent parts of the argument. The kernel property asserts exactness and the left monomorphism without asserting epimorphy; the quotient lemma asserts only epimorphy and is proved. Checked zero G, torsion G, negative z, and characteristic two in the local calculations: the coordinate inverse, rather than flatness, gives the splitting. Added complete source-bearing docstrings and verbatim Lean records. Searches through msearch leansearch, leanfinder, loogle, grep and local rg found no exact duplicate. Leansearch is unavailable (Internal Server Error). The upstream ProjectiveLine.koszul_shortExact has different projective-space objects and does not directly supply the present tensor statement; its local method informs the proved quotient lemma.
4. Checked the shortest available local route. The quotient proof reuses Proj.isIso_restrict_twistMul and Scheme.Modules.epi_of_surjective_stalk; it adds no lower hole. The new modules have minimal statement imports and plain proof imports. The report lists both old proof dependencies that are no longer direct. Read dag/units/sk-thm-picard-duality.json: its realized fields are unchanged and this below-unit split bypasses no realized step.
5. Updated the target node's proof, proof_deps and proof_origin to the categorical combination. Repaired both new nodes with self-contained statements, acyclic proof dependencies, complete local proofs, three search kinds, and complete Lean records. Their dependencies agree with the declarations and constructions used.

Second reading changed: proved quotient epimorphy; repaired docstrings, nodes, imports, warning, and progress accounting. The kernel-fork proof is still open.

Axiom checks: `proj_coordinate_quotient_epi` uses only `propext`, `Classical.choice`, and `Quot.sound`. `exists_proj_coordinate_kernel_fork` and `exists_proj_coordinate_shortExact` use those plus `sorryAx`, exactly as expected from the single remaining kernel hole. All three modules compile without warnings.

The first dry run passed preflight, but its automated quotient-module axiom probe hit 60 seconds; the separate #print axioms check had succeeded. Replaced the manual monoidal naturality rewrite with Mathlib's `Functor.Monoidal.map_whiskerLeft` in a private fully proved categorical helper, to reduce the proof term checked by the kernel. The quotient module now compiles in 38.6 seconds.
