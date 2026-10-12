## What changed

Proved `AlgebraicGeometry.exists_derivedDirectImage_coproduct_affine_truncation`
without changing its signature. Added the proved theorem
`AlgebraicGeometry.exists_isIso_schemeHigherDirectImage_uniform_truncGE_over_affine`
in `Sheaf.AlgebraicGeometry.DerivedDirectImageUniformAffineTruncation`. Its uniform
quantifier precedes the object: the bound depends on f, q and U only.

The main proof applies the existing ambient quasi-coherent coproduct closure to S,
then the uniform affine bound to S and all summands. Restriction preserves coproducts;
coproduct comparison naturality makes the restricted Sigma.map invertible. Evaluation
at the terminal object of Over U gives exactly the two requested evaluation maps.
Sections are never assumed to preserve coproducts.

The new theorem is also fully proved. Restriction preserves quasi-coherent cohomology.
Apply the uniform upper bound to the restricted qcqs morphism with affine target.
Shift the upper truncation tail by -n-1, with n=N-q, to an object with no positive
cohomology. Shift compatibility gives vanishing in degrees q and q+1, and the mapped
truncation triangle gives the canonical map isomorphism. Natural open restriction,
exact restriction's homology comparison, and its truncation comparison transport
this to the actual canonical projection in the stated carrier. Standard derived
categories are chosen only for the two open subschemes; the original universes and
instances remain unchanged.

Both modules compile together cleanly with lcompile.py. No axiom or definition was
added. The two node proof routes match the Lean. Proof-only imports are nonpublic.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.exists_derivedDirectImage_coproduct_affine_truncation`
(node `lem-pc-derived-direct-image-coproduct-affine-truncation`).

Also proved the new auxiliary theorem
`AlgebraicGeometry.exists_isIso_schemeHigherDirectImage_uniform_truncGE_over_affine`
(node `lem-pc-derived-direct-image-uniform-affine-truncation`).

No sorry remains in either delivered module; no holes added or split off. The proof
uses the existing uniform truncation bound and open restriction declarations, whose
own remaining dependency holes are outside this delivery. This is closure of one
original hole from existing named dependencies, not an axiom-free closure of the
entire import graph.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums`:
  `lem-pc-derived-ambient-direct-sums` is already used inside the existing coproduct
  closure proof; this delivery need not reconstruct representatives.
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum`:
  `lem-weil-pbc-quasi-coherent-module-direct-sum` is not needed; the existing closure
  uses the source library's proved arbitrary-sum quasi-coherence theorem.
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`:
  `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections` is not needed for the
  same reason; no finite-partial-sum filtered-colimit presentation is built.
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`:
  `lem-sc-derived-k-injective-restrict-open` is used inside the existing open
  restriction comparison, not directly in either delivered proof.
- `Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound` is moved from
  the main module's imports into the auxiliary proof. Its node remains needed.

The objectwise `DerivedDirectImageAffineTruncationComparison` is not imported:
its existential object-dependent bound cannot give this familywise bound.
`DirectImageTruncationTailBound` is not imported: the short shift argument is
written directly in the new proof. Its declaration was absent from the local
compiled build while its source was present; no duplicate theorem was introduced.
These are removed direct dependencies, not a claim that no other target uses them.

## Where the brief, the DAG or earlier work was wrong

The planned finite-sums/filtered-colimit construction is unnecessary because
`schemeDerivedQCohClosedUnderCoproducts` already proves the required closure.
The stated uniform-bound theorem's second clause alone is not sufficient: its
bound is object-dependent. The first clause supplies the uniform N used here.

The local checkout lacks `literature/stacks-project/perfect.tex`; the source was
read from Stacks Tags 08D5 and 08DZ at their official pages. No mathematical error
in the statement was found. Empty index types require no choice of summand; the
coproduct comparison proof handles them. The zero object, empty affine open,
arbitrary integer q, and noncompact Y introduce no extra hypotheses.

No unit statement or realized unit step was bypassed. The unit record
`sk-thm-picard-duality` has no realized node for this auxiliary route.

## New nodes

`lem-pc-derived-direct-image-uniform-affine-truncation`, in the item's chapter and
unit, records the proved single-object uniform affine bound. It contains no
coproduct, cofan, or evaluation assertion: these are assembled by the main proof.
It is fully proved, introduces no sorry, and is strictly a component of the
original argument. Three kinds of Mathlib search were run (LeanSearch returned
HTTP Internal Server Error; LeanFinder returned general truncation lemmas; grep
found no exact result). Existing blueprint search found no uniform truncation
node. No change record is required: all existing statements and definitions,
including the target interface, are unchanged.

## Second reading by V1

1. Compared the delivered main module against the repository with diff. Its only
   changes are proof imports and the proof body: the existing theorem signature
   and docstring are byte-for-byte unchanged. No existing definition or statement
   is changed, and no change record is needed. The auxiliary module is new. PASS.
2. Compiled both modules together in import order through lcompile.py: clean,
   without errors or warnings (23.7 s and 17.4 s). Scanned both source files for
   sorry, axiom, unsafe, opaque, implemented_by, extern and skipKernelTC: none.
   Scratch-copy #print axioms for both public theorems reports exactly propext,
   Classical.choice, Quot.sound and sorryAx. The last is inherited from existing
   open dependencies, not introduced by either delivered proof. No definitions
   are added, so there is no arbitrary data witness or hollow construction. The
   chosen open-restriction natural isomorphism is used only inside the theorem
   proof to transport invertibility; no public data construction depends on it.
   PASS as a closure of this item's hole, not an axiom-free target closure.
3. No statements are split off with sorry. Read the fully proved new uniform
   affine theorem and its docstring. The bound N is chosen before E, n=N-q, and
   the shifted tail is nonpositive; N <= j+n+1 holds for j=q and j=q+1. The mapped
   triangle therefore proves invertibility of the canonical projection. Exact
   restriction and naturality transport that very map. Zero objects, empty U,
   negative q and arbitrary unbounded E require no additional hypotheses. This
   is a strict component of the item, without coproduct or evaluation assertions.
   Independently searched LeanFinder for cohomological amplitude and uniform
   projection bounds, Loogle for functorial isomorphism preservation, msearch
   grep for truncGEπ, and the library for uniform truncation and affine
   comparisons. No existing theorem replaces it: the affine comparison has
   objectwise quantifiers, and the existing tail-bound theorem is still sorry
   in the repository. PASS.
4. Read top-down from the main proof through the uniform bound, restriction and
   ambient QCoh closure. The coproduct closure uses the given IsColimit, hence
   applies to S and handles empty I. sigmaComparison naturality and preservation
   by restriction prove invertibility before evaluation; sections are not
   assumed to preserve coproducts. Imports added for proofs are plain import.
   Every old proof dependency removed from the direct route is covered in
   No longer needed, including dependencies retained indirectly. The unit's
   realized statement and step lists are empty, so no realized unit route is
   bypassed. No shorter applicable proved library theorem was found. PASS.
5. Compared the old and new existing-node JSON: only proof, proof_deps and
   proof_origin change. Read both delivered nodes against the Lean. Their steps
   and dependency unions agree with the actual proofs; the new node records the
   verbatim signature, source, natural-language proof, searches, chapter/unit,
   creation data and blueprint provenance. PASS.

Second reading changed only this report: added the independent checks and the
explicit axiom/dependency qualification. No repair to the Lean or nodes was needed.
