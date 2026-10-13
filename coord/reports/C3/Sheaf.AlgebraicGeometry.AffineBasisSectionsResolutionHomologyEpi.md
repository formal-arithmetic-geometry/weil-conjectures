## What changed

Added the proof of `affineBasisSections_resolution_homology_epi` using naturality of
`ShortComplex.mapHomologyIso_hom_naturality`. Added a complete finite acyclicity lemma
and a named K-injective tower lemma. The latter remains the sole sorry.
The private finite helpers reuse the proven arguments in
`ShortComplexSectionComparison` and `SectionAcyclicIncomingKernelImage`, with
integer indexing and the differential-cokernel exact sequence replacing induction.

## Proved and sorry left

Proved `affineBasisAcyclicSections_preservesLeftHomology` and
`affineBasisSections_resolution_homology_epi`. The new theorem
`affineBasisKInjectiveSections_preservesLeftHomology` remains `sorry`, with node
`lem-sc-affine-basis-kinjective-sections-preserves-homology`.
This is a decomposition: one original hole closed, one smaller hole added (net zero);
the finite preservation theorem is proved with no direct sorry.

## No longer needed

No existing Lean import was removed, since the original module had only public
statement imports. The new proof imports are private. The original node's direct plan dependencies on the affine-open basis, restriction
K-injectivity, derived-limit lemmas, injective-module acyclicity, K-injective Hom
comparison, and existence of K-injective resolutions are not imported by the final
proof. They are replaced by the two named homology-preservation interfaces.

The original node no longer directly uses:
- lem-pc-derived-limit-eventually-iso;
- lem-pc-derived-limit-milnor-sequence;
- lem-sc-derived-k-injective-restrict-open;
- lem-weil-pbc-affine-opens-basis;
- lem-weil-pbc-injective-module-sheaf-H-acyclic;
- lem-weil-pbc-kinjective-hom-derived;
- prop-pur-kinjective-resolutions-exist.

The first three remain dependencies of the split K-injective interface. This delivery
claims no removal of their modules from the whole target closure.


## Where the brief, the DAG or earlier work was wrong

The DAG's direct proof plan omits the finite homology-preservation interface needed to
identify the actual evaluation homology map. The finite part can be proved without term
acyclicity: differential-cokernel and homology acyclicity suffice by two short exact
sequences. The unbounded tower argument is isolated as one strictly smaller theorem.

## New nodes

`lem-sc-affine-basis-acyclic-sections-preserves-homology` records the complete finite
long-exact-sequence reduction. `lem-sc-affine-basis-kinjective-sections-preserves-homology`
records the remaining compatible truncation-tower argument and is the only new sorry.

The unit realization lists are empty for this local supporting node; no unit statement
or required realized step is bypassed. Edge cases checked: empty V and zero complexes
give zero section homology; the integer sequence argument needs no initial degree.
No definition or existing signature changes, and no forced adaptations.


## Second reading by C3

1. Compared the item module with the repository using diff, and compared the existing
   node records field by field. The existing theorem signature is byte for byte
   unchanged; the node changes only proof, proof_deps and proof_origin. No existing
   definitions or visibility changed. Verdict: pass.
2. Compiled all three modules locally in import order. A scratch axiom probe found only
   propext, Classical.choice and Quot.sound for
   `AlgebraicGeometry.affineBasisAcyclicSections_preservesLeftHomology`. The item and
   K-injective interface additionally use sorryAx, as expected from the sole named
   remaining hole. Scanned all delivered Lean for forbidden declarations and hollow
   definitions: none. Verdict: pass as a decomposition, not a completed target proof.
3. Read both new statements and their complete docstring arguments. The finite proof
   uses H -> differential cokernel -> outgoing image and incoming image -> cycles -> H;
   only V itself is needed. The remaining K-injective interface concerns one complex,
   without a resolution map or differential-cokernel assumptions, and isolates the
   unbounded derived-section comparison rather than restating the item. Empty V and
   zero complexes give zero objects; an acyclic K-injective complex is contractible,
   so additive sections have zero homology. Fresh msearch searches (leanfinder for
   K-injective section comparison, loogle for mapHomologyIso, grep for acyclic homology)
   and rg on the local library found interfaces but no duplicate geometric theorem.
   No short existing proof of the tower interface was found. Verdict: pass.
4. Read every helper in the finite module and the final naturality reduction. It proves
   an isomorphism and hence the required epimorphism. Public imports supply actual
   signature names (including moduleRings and PreservesLeftHomologyOf); the imports
   needed only by proofs are private. An import-removal probe confirmed that
   QuasicoherentKernel is needed for PreservesFiniteLimits of restrictFunctor; without
   it the finite proof fails to synthesize that instance. The unit realization is statement=[] and
   steps=[[]], so no realized unit step is bypassed. Verdict: pass.
5. Checked the new nodes' signatures against Lean, their source, search, creation,
   blueprint and dependency fields, and the item's two preservation dependencies
   against the proof. Existing node statements are unchanged. Verdict: pass.

Second reading added this review, explicitly enumerated all seven former direct
proof dependencies below, and clarified the K-injective docstring source argument.
Tag 08D4 requires quasi-coherence and is not directly applicable; its tower argument
is reused with convergence from Tag 071B and the actual homology-sheaf vanishing.
No Lean proof or signature changed. Source checks: https://stacks.math.columbia.edu/tag/071B
and https://stacks.math.columbia.edu/tag/08D4 (local literature files absent).
