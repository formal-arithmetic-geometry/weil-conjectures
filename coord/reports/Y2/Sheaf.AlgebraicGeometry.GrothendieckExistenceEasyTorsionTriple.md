## What changed

Replaced the sorry in
`AlgebraicGeometry.grothendieckExistenceEasy_torsionTriple` by a complete Lean reduction.
Its existing signature and public imports are unchanged. No existing definitions or
statements, including Challenge declarations, were changed. No forced adaptations.

The reduction follows the corrected parent node's route. First it applies
`coherentFormalModule_annihilated_iff` (conditions 1 and 2) to obtain the affine limit
annihilation hypothesis. A new construction lemma supplies one actual torsion-controlled
triple. A second new lemma lifts a completed morphism between torsion-controlled arrows
to a unique coherent morphism. The item's proof constructs forward and reverse lifts,
proves both composites are identities by uniqueness of identity lifts, builds the
isomorphism, checks both required equations, and proves uniqueness using Iso.ext.
This categorical combination is proved in Lean, with no sorry in its proof body.

New modules:
- `Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction`
- `Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLift`

Updated the parent's proof, proof_deps and proof_origin, and added complete node records
for the two new statements. Each statement has its own public theorem, source, proof
in words and exactly one named sorry. Existing planned proof dependencies are retained
in these new modules; they are not claimed to be proved here.

All three modules compile through lcompile.py. The item compiled without warnings
following removal of an unused simp argument. The final dry run performs compilation,
axiom and preflight checks. No push is authorized or attempted by this worker.

## Proved and sorry left

Original holes closed: 1 of 1, by name:
`AlgebraicGeometry.grothendieckExistenceEasy_torsionTriple`
(node `lem-weil-pbc-easy-algebraization-torsion-triple`).
There are no sorries left in the item's module.

New holes added: 2, by name:
- `AlgebraicGeometry.torsionControlled_algebraization_construction`
  (node `lem-weil-pbc-torsion-controlled-algebraization-construction`). This is only
  existence and actual torsion control, from affine limit annihilation. It asserts
  neither uniqueness nor that an arbitrary algebraization has actual torsion.
- `AlgebraicGeometry.torsionControlled_completion_hom_lift`
  (node `lem-weil-pbc-torsion-controlled-completion-hom-lift`). This is reconstruction
  of one coherent morphism from a completed morphism and two actual torsion-controlled
  arrows to a fixed target. It constructs no algebraization object, accepts noninvertible
  formal morphisms, and does not assert isomorphism of sources.

This is a decomposition, not a claim that the entire mathematical theorem is proved
without sorry dependencies. Holes closed minus newly added holes is -1 for this delivery.
The final isomorphism and its uniqueness are genuine consequences proved in the item;
neither new theorem repeats its full hypotheses and conclusion.

## No longer needed

Removed direct proof imports from the item's module:
- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.RingTheory.FiniteIffFormalGlueing`
- `Sheaf.RingTheory.FormalGlueingComplexExact`
- `Sheaf.RingTheory.FormalGlueingIsogeny`
- `Sheaf.Topology.GlueSheavesOfModules`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`

These dependencies belong to the construction and comparison lemmas' proof plans.
The following old nodes are no longer direct proof dependencies of the parent
(they remain in the new construction/comparison proof plans):

- `def-weil-module-base-change`
- `def-weil-pbc-adic-completion`
- `def-weil-pbc-coherent-formal-module`
- `def-weil-pbc-module-localization-away`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-adic-completion-mod-ideal`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-coherent-formal-modules-local-exactness`
- `lem-weil-pbc-completion-finite-module-tensor`
- `lem-weil-pbc-formal-glueing-complex-exact`
- `lem-weil-pbc-formal-glueing-finite-modules`
- `lem-weil-pbc-formal-glueing-isogeny`
- `lem-weil-pbc-glue-sheaves-of-modules`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-noetherian-completion-flat`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-quasi-coherent-module-kernel`
- `pqf-def-coherent`
- `pqf-def-locnoeth`
- `pqf-lem-coherent-ft-locnoeth`

No original proof-plan node is globally unnecessary: its use is recorded in those two
new nodes, or in their statement dependencies. No module is claimed pruned from the
targets' import closure. Only the item's direct dependency list is shortened.

The invalid earlier shortcut is not imported: neither
`Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy` nor the withdrawn
`TorsionTripleActualKernelCokernel` occurs in the new proof. No unit route is bypassed;
`dag/units/sk-thm-p1.json` realizes neither this parent node nor the two new nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier reduction was false at the unit ideal. Completion forgets modules supported
away from V(J), so componentwise torsion does not imply actual torsion for an arbitrary
chosen algebraization. Unrestricted uniqueness in grothendieckExistenceEasy also fails.
The new construction lemma existentially constructs a suitable arrow; the comparison
lemma requires actual torsion on both arrows. Neither uses the false implication.

Edge cases checked for both new statements:
- J = the unit ideal: formal completions are zero, but an actual torsion-controlled
  arrow has zero kernel and cokernel, hence is an isomorphism. The construction chooses
  F = H and its identity arrow. Comparison is a followed by the inverse of a'.
- J = the zero ideal: formal systems are constant up to canonical isomorphism; the
  formal morphism is already a coherent morphism. Every actual kernel and cokernel
  is annihilated by the first power of J.
- X empty: all morphisms are unique and the positive exponent can be 1.
- H = 0: the new statements still require actual ideal-power torsion on their coherent
  sources. They do not introduce arbitrary invisible summands.
- No properness or completeness of X is assumed or used. Affine formal gluing provides
  maps by combining completion with the complement of V(J).

The local literature source mirror is absent on this machine. WANTED:
`literature/stacks-project/coherent.tex`, Tag 0889(1) and Remark 0888, for the parent and
both new nodes; `literature/stacks-project/more-algebra.tex`, Tags 05EK, 0ALK and 05EU,
for both new nodes. The proofs in words are agent expansions of the existing parent
plan, checked against the online Stacks pages 0889, 0888, 05EK and 0ALK. Accordingly
proof_origin.by is agent. No literature was downloaded into the read-only repository.

LeanSearch returned Internal Server Error for both new-node queries; this is recorded
as unavailable, not as evidence of absence. Loogle/LeanFinder and Mathlib source grep
were successful. Searches of both Lean roots, the DAG and the blueprint found no
existing theorem with either new signature.

## New nodes

`lem-weil-pbc-torsion-controlled-algebraization-construction` covers the parent's
steps 1--3 and the construction/gluing portion of step 5. Its statement is existence
with actual kernel/cokernel torsion, assuming the affine limit condition supplied by
Remark 0888. Its proof plan uses the affine dictionary, completion algebra, formal
isogeny, finiteness, comparison lifts and coherent sheaf gluing.

`lem-weil-pbc-torsion-controlled-completion-hom-lift` covers the morphism reconstruction
part of step 4 and local-to-global morphism descent in step 5. It does not require a
formal isomorphism: the actual arrows to H give the maps on the complement of V(J),
and 05EK reconstructs a unique map from those and the completed map. Its uniqueness is
then used in the main module to prove inverses and uniqueness of isomorphisms.

No change records are needed because no existing interface is changed.

## Second reading by Y2

1. Compared the item with the read-only repository by diff: its entire existing
   declaration signature, docstring and public imports are byte-for-byte unchanged.
   Only its proof and private proof imports differ. The two other modules are new;
   there are no changed definitions, target statements or forced adaptations. PASS.
2. Independently compiled all three modules with lcompile.py in import order, with
   no errors or warnings. Exactly the two reported public named theorems have sorry;
   the parent has a complete categorical proof. No axiom, unsafe, opaque, extern,
   implemented_by or hollow definition occurs in the delivery. Independently printed
   the axioms of all three declarations: only propext, Classical.choice, Quot.sound
   and the expected sorryAx from the reported open dependencies. PASS.
3. Read both split-off statements and their proof docstrings against
   [0889](https://stacks.math.columbia.edu/tag/0889),
   [0ALK](https://stacks.math.columbia.edu/tag/0ALK),
   [05EU](https://stacks.math.columbia.edu/tag/05EU) and
   [05EK](https://stacks.math.columbia.edu/tag/05EK).
   Construction is existence only, with affine limit torsion as input; comparison
   reconstructs a possibly noninvertible morphism, not an algebraization object.
   Each is strictly a part of the argument and has a matching node and a complete
   proof in words. Independently checked zero ideal, unit ideal, empty scheme and
   zero target. Actual torsion on the arrows is essential: no arbitrary invisible
   algebraization is asserted to have torsion. Localized inverses and the injective
   exact gluing complex justify comparison; the kernel/cokernel comparisons in 0ALK
   transfer bounded torsion to the constructed arrow. No data definition chooses an
   arbitrary witness from an unproved existence statement. PASS.
   Fresh msearch queries used different words: LeanFinder on descent from completion
   and the complement of an ideal's vanishing locus, Loogle on AdicCompletion.map,
   and grep on formalGlue/formalGluing/formalGlueing/isogeny. Results were completion
   tensor comparison and functoriality, with no exact gluing/algebraization theorem.
   Searched both Lean roots and inspected CompletionInternalHomAffineSectionsLift:
   it lifts into a completed internal Hom, not into an actual coherent module, so
   it does not close either hole. Neither split-off proof closes in a few minutes.
4. Checked the parent proof from its conclusion downwards: it uses the existing
   annihilation equivalence, construction and unique forward/reverse lifts. The
   identity-lift argument proves both inverse identities; the final uniqueness is
   uniqueness of the hom followed by Iso.ext. Its imports are precisely those used.
   The new modules retain proof-plan imports for their open arguments; the public
   ModuleCat limits import in construction supplies limit objects in its signature.
   All removed original imports and all removed parent proof_deps are now explicitly
   listed above; none is globally pruned. Inspected sk-thm-p1.realized: no realized
   statement or step is bypassed or edited. PASS.
5. Compared the parent JSON with the repository: exactly proof, proof_deps and
   proof_origin change. For all three nodes, proof_deps equals the union of the
   proof steps' uses. Checked new-node source, search records, created, blueprint,
   chapter, unit and Lean declaration/signature records against the modules. PASS.

Second reading changed only this report: added the exhaustive removed-parent-node
list and this independent review. No Lean or node repair was needed. The delivery
closes one original hole and adds two strictly smaller holes; this is a decomposition
with net -1 holes closed, not an axiom-free proof of the mathematical theorem.
