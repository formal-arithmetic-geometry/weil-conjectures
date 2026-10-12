## What changed
The existing declaration `AlgebraicGeometry.closedImmersion_formalKernel_annihilated`
keeps its exact signature, visibility, and docstring. Its proof now takes the
inverse-system isomorphism from `closedImmersion_formalKernel_comparison`, derives
quasi-coherence of the coherent terms, and applies the proved
`Scheme.closedImmersion_idealPower_annihilation` to each component and `hkill`.
All three added imports in the existing module are proof-only.

The second reader removed the proposed `ClosedImmersionFormalKernelAnnihilationAux`
module and node: its existential witness could be the kernel itself, so it only
repackaged the target. Two genuine intermediate modules replace it:
`ClosedImmersionFormalKernelComparison` contains only the categorical kernel
comparison, and `ClosedImmersionIdealPowerAnnihilation` proves the affine
annihilation calculation for ordinary quasi-coherent modules without Noetherianity
or any formal-kernel hypothesis. No existing statement or definition changed and
no change record is needed.

## Proved and sorry left
Hole closed: `AlgebraicGeometry.closedImmersion_formalKernel_annihilated`
(node `lem-weil-pbc-closed-immersion-formal-kernel-annihilation`).
Hole added: `AlgebraicGeometry.closedImmersion_formalKernel_comparison`
(node `aux-closed-immersion-formal-kernel-comparison`), whose whole proof is `by sorry`.
No other delivered declaration has a hole. This is a decomposition: one existing
hole closed and one strictly smaller hole added, net zero direct holes. The
categorical comparison still needs the geometric affine/local formal-kernel argument.

New theorem with a complete Lean proof:
`AlgebraicGeometry.Scheme.closedImmersion_idealPower_annihilation`
(node `aux-closed-immersion-ideal-power-annihilation`). It uses the existing affine
product-section and zero-product theorems, some of which remain open upstream.
All three files compile without errors or warnings. Individual `#print axioms`
checks show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for all
three declarations; this is not a fully axiom-free proof of the target.
No ledger net reduction or library module pruning is claimed.

## No longer needed
No existing module imports were removed; no library module is claimed pruned.
The undelivered equivalent-to-target auxiliary module and node were discarded.

Every old direct `proof_deps` entry is accounted for:
- `lem-weil-pbc-closed-immersion-coherent-equivalence`,
  `lem-weil-pbc-coherent-formal-modules-affine`, and
  `lem-weil-pbc-coherent-formal-modules-local-exactness` are now dependencies of
  the pure kernel-comparison node, retained as its proof-dependency imports.
- `def-sbc-closed-immersion-ideal-sheaf` and
  `lem-weil-pbc-ideal-power-product-zero-affine-cover` are now dependencies of
  the proved ideal-annihilation node.
- `lem-weil-pbc-coherent-formal-modules-abelian` is no longer directly used as a
  theorem: the original Abelian structure is already a parameter of the target
  and the comparison. Its module remains reached through local exactness; this
  is not a claim to prune it from the library.
The existing node's direct proof dependencies are the two new intermediate nodes
and `pqf-lem-coherent-ft-locnoeth`, exactly as used in the new Lean proof.

## Where the brief, the DAG or earlier work was wrong
The first worker's auxiliary theorem was equivalent to the whole target: from the
target one obtains its conclusion by taking K = kernel(a), q = Iso.refl, and
identity product isomorphisms; conversely its IsZero witnesses give the target.
It was not a strict subproblem, and its docstring supplied no complete proof.
The new comparison has neither the ideal L nor exponent t nor hkill, and the
ordinary-module annihilation step is proved separately. The first worker's claim
that the target was proved is therefore replaced by an explicit decomposition count.

## New nodes
`aux-closed-immersion-formal-kernel-comparison`, in
`Sheaf.AlgebraicGeometry.ClosedImmersionFormalKernelComparison`: the pure
inverse-system comparison for a categorical formal kernel under closed pushforward.
The docstring gives the affine restriction-of-scalars and global kernel argument.
The node retains the old geometric dependencies and cites verified source labels
`lemma-i-star-equivalence` (087T), `lemma-inverse-systems-affine` (087W), and
`lemma-inverse-systems-abelian` (087X), in Stacks `coherent.tex`.

`aux-closed-immersion-ideal-power-annihilation`, in
`Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerAnnihilation`: proved transport
of ideal-power annihilation for a quasi-coherent module and an isomorphic closed
pushforward. Its proof is the affine section calculation and sheaf separatedness.
The source's closed quotient replacement is
`theorem-grothendieck-existence` (088E).

Both new nodes have self-contained statements, verbatim Lean signatures, proof
steps and their dependency unions, creation records, and blueprint provenance.
Real Mathlib searches are recorded in searches.jsonl; LeanSearch was unavailable
(HTTP 500), not a no-match verdict. LeanFinder/Loogle and local source searches
found generic scalar, ideal map, and kernel facts, not these sheaf statements.

## Second reading by E2
1. Compared the delivered existing module with the repository using diff. Only
   proof-only imports and the proof body changed; the existing declaration's
   signature, docstring, universes and visibility are byte-for-byte unchanged.
   No other existing Lean module is delivered. Verdict: pass.
2. Compiled each of the three delivered modules in import order using lcompile.py.
   Compiled scratch copies with individual #print axioms checks. Only the allowed
   three axioms and sorryAx occur, with the open comparison and upstream section
   lemmas explicitly reported above. The only direct hole is the named comparison;
   there are no new definitions, data choices, forbidden declarations or escape
   attributes. Verdict: pass as a decomposition, not a completed target proof.
3. Rejected and removed the original auxiliary restatement. Read both replacement
   statements and their proofs against Stacks 087T, 087W, 087X and 088E and the
   existing imported declarations. The comparison concerns formal categorical
   kernels, not levelwise kernels. Identity immersions reduce it to uniqueness of
   kernels; empty schemes and zero source/target systems pose no exceptions. For
   annihilation, t = 0 forces F = 0, t = 1 is the ordinary ideal case, L = 0 gives
   annihilation by j.ker for positive t, and empty schemes are covered by the
   affine-basis criterion. Neither statement assumes proper support. Searched
   Mathlib with alternative terms using msearch.py and searched lean/Sheaf,
   lean/WeilConjectures, and the upstream algebraic-geometry sources. No duplicate
   statement was found. Verdict: true, needed, and strictly separated subproblems.
4. The shortest available section calculation is used for annihilation. The
   unresolved geometric comparison retains the affine and local-exactness route.
   Checked dag/units/sk-thm-p1.json realized: none of the affected nodes realizes
   a unit statement or step, and no realized route is removed. Existing public
   imports are required by the unchanged API; new proof imports remain private
   to proofs. The remaining comparison imports carry its planned dependencies.
   All old proof dependencies are accounted for under No longer needed.
   Verdict: pass; no library module pruned.
5. Checked the existing node's proof, proof_deps and proof_origin against the two
   explicit applications and coherence criterion in Lean. Checked both new nodes'
   signatures against their modules and proof_deps against the unions of uses;
   no statement dependency points back to the parent, so the original auxiliary
   cycle is also avoided. Verified Stacks source labels from coherent.tex.
   Verdict: pass.

Changes made by this second reading: replaced the auxiliary restatement with a
pure formal-kernel comparison and a proved ordinary-module annihilation theorem;
rewrote the target proof to combine them; corrected node metadata and source
labels, recorded actual searches, and corrected progress and dependency reporting.
