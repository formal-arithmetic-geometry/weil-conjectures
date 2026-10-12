## What changed

The item now proves the quasi-isomorphism conclusion from a separated construction theorem and a fully proved local pushout kernel comparison. Two intermediate public theorems were added: `exists_subcategory_right_resolution_system` records the ascending pushout system, and `exists_complex_of_cokernel_pushout_system` records the remaining assembly step. The local helper `quasiIsoAt_of_pushout_factorization` is proved without sorry. The system theorem is proved by explicit pushout construction and natural-number recursion. Only the assembly theorem remains sorry for a follow-up worker. Imports were added for the pushout kernel API and the two intermediate modules.

## Proved and sorry left

One original hole closed; one strictly smaller assembly hole added. This is a decomposition, not an axiom-free proof of the complete resolution theorem.

Proved: `CochainComplex.exists_subcategory_right_resolution_system`, its private initial frontier, extension and recursion, `CochainComplex.quasiIsoAt_of_pushout_factorization` (private helper) and the original theorem `CochainComplex.exists_mono_quasiIso_in_subcategory`, by applying the separated system theorem and the kernel comparison.

Sorry left: `CochainComplex.exists_complex_of_cokernel_pushout_system` in `SubcategoryRightResolutionAssembly.lean`, node `lem-weil-pbc-subcategory-right-resolution-assembly`.

## No longer needed

The parent theorem no longer directly needs `def-weil-pbc-category-colimit`, `lem-weil-pbc-abelian-exact-epi-cokernel`, `lem-weil-pbc-abelian-pushout-mono`, `lem-weil-pbc-pushout-cokernel-iso`, or `lem-weil-pbc-cokernel-map-mono-of-mono`: these remain needed by the now-proved separated construction theorem, so they are not globally pruned. No imports from the repository version were removed; no stated dependency node was removed from the mathematical route. During second reading, the two new modules replaced the unnecessarily broad public QuasiIso and ShortComplex.Abelian imports with public ShortComplex.HomologicalComplex. The assembly module no longer imports CommSq; the system and parent import it privately for proofs. No module is globally pruned. The construction and assembly nodes make the remaining work explicit.

## Where the brief, the DAG or earlier work was wrong

The original DAG names ascending recursion in step 6 but supplies no Lean declaration for its assembly into a complex. Lean's indexed complex API requires the assembly to be stated separately from the finite pushout step, so the delivery isolates the assembly gap. The finite construction and its recursion are fully proved. The cohomology step is shorter than the prose plan: Mathlib's `Abelian.epi_kernel_map_of_isPushout`, kernel cancellation, and `homologyIsKernel` close it directly.

## New nodes

`lem-weil-pbc-subcategory-right-resolution-system` records the explicit recursive pushout system and is stated in `lean/Sheaf/Algebra/Homology/SubcategoryRightResolutionSystem.lean`.

`lem-weil-pbc-subcategory-right-resolution-assembly` records the assembly of the natural-number system into an integer-indexed complex and is stated in `lean/Sheaf/Algebra/Homology/SubcategoryRightResolutionAssembly.lean`.


## Second reading by M1

1. Compared the parent module with the repository version: the existing public theorem's
   signature and original imports are byte for byte unchanged. Its body now has a real
   reduction through the constructed system and an independently proved homology/kernel
   comparison. The other two modules and their declarations are new. There is no existing
   definition or statement change and no change record is required. Verdict: pass.
2. Compiled all three files in import order, with no errors or warnings. The only literal
   sorry is the whole proof of the public assembly theorem listed above. There is no axiom,
   unsafe, opaque, extern, implemented_by or hollow definition. Scratch-copy #print axioms
   checks give only propext, Classical.choice and Quot.sound for the private initial,
   extension, recursion and kernel-comparison declarations. The parent and system theorems
   additionally have sorryAx through the assembly theorem; the assembly theorem has the
   same permitted list plus sorryAx. The noncomputable definitions choose embeddings from
   the supplied hembed hypothesis, not from an unproved mere-existence theorem. Verdict:
   pass as a decomposition, not an axiom-free proof of the parent.
3. Read both new statements, their docstrings and nodes. The assembly gap is strictly the
   gluing/transport part of the argument: it assumes actual terms, maps, mono invariants,
   cokernel universal properties and pushout squares, and asserts no quasi-isomorphism.
   The finite extension and natural-number recursion producing these inputs are proved.
   Checked consecutive differentials via d_m p_(m+1)=0 and factorization of d_(m+1).
   At a the incoming differential is zero and p_0 is an isomorphism. At a-1 both opcycles
   objects are zero and the identity on K.X a gives the boundary pushout with embedding
   alpha_0; at smaller degrees all terms are zero. These checks also cover an all-zero K
   and arbitrary integer a. Independent leanfinder, loogle and grep searches, with new
   wording, found constructors and extension/opcycles APIs but no duplicate statement.
   Also searched lean/Sheaf and lean/WeilConjectures. The remaining assembly needs substantial
   indexed transport work rather than a quick local proof. Verdict: pass.
4. Read the original proof-dependency nodes and their Mathlib matches and the sk-thm-p1
   unit realized fields. The proof retains the pushout/cokernel construction and uses the
   matched Mathlib declarations directly for kernel comparison. No unit statement or step
   is bypassed. The No longer needed section names all five old dependencies absent from
   the parent's new proof_deps; they remain in the system node. No old import or globally
   reachable module was pruned. The new modules now expose only imports needed by their
   signatures, and their proof imports are private. Verdict: pass after import cleanup.
5. Checked all three node proof plans, proof_deps unions, proof_origin, Lean records and
   new-node provenance against the files. The parent node describes the kernel comparison;
   the system node describes the actual initial frontier, successor cokernel map and
   explicit recursion; the assembly node describes the one remaining hole. The two new
   nodes have complete source, proof, search, blueprint, creation and Lean fields. Verdict:
   pass, with independent search evidence appended to both new nodes.

Changed only import cleanup, the new system theorem's docstring (its actual construction
starts at a, not a-1), search evidence and this report. No proof or signature needed repair.
One original hole closed: CochainComplex.exists_mono_quasiIso_in_subcategory. One hole added:
CochainComplex.exists_complex_of_cokernel_pushout_system. Net zero; decomposition only.
