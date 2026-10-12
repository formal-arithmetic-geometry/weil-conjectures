## What changed

Preserved the signature and docstring of
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_kernel` byte for byte.
Replaced the first worker's conjunction-only split with a stalkwise reduction.
The target proves the zero composite on sections, detects exactness on stalks,
and applies `ShortComplex.Exact.fIsKernel` to the monic image inclusion.
It uses `module_stalk_exact` and `Abelian.imageIsoImage` to identify the range
of the categorical image inclusion, without importing the holed `StalkImageRange`.

`ClosedImmersionUnitEpi` is now proved: the canonical unit is surjective on
stalks by `closedImmersion_pushforward_stalks`, `exists_tensorPullback_stalk_iso`,
`i.stalkMap_surjective`, and Mathlib `TensorProduct.mk_surjective`. Stalk
surjectivity and `TopCat.Presheaf.section_ext` give cancellation, hence epi.
`Adjunction.unit_leftAdjointUniq_hom_app` transports this to the chosen unit.
Only TensorPullback and ClosedImmersion are public imports of that helper;
all imports used only by its proof are plain imports.

Deleted the unsubmitted `ClosedImmersionUnitKernelFork` module and node.
Added `ClosedImmersionUnitStalkKernel`, a local range equality for the
multiplication map itself, with its complete stalkwise proof in the docstring.
It has no epi assertion, no categorical image assertion, and no kernel
universal property. The target supplies the remaining global argument.
Updated the target DAG node's proof, proof_deps and proof_origin to match.
No statement or definition changes, change records, or forced adaptations.

## Proved and sorry left

Hole closed in the original item:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_kernel`
(node `lem-weil-pbc-closed-immersion-unit-kernel`). Its body is now a reduction,
not a complete sorry-free proof of the mathematical result.

Additional declaration proved without sorry:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_epi`
(node `lem-weil-pbc-closed-immersion-unit-epi`). This closes the first worker's
epi hole; it was not a separate hole on the repository baseline.

Exactly one hole added and left:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_unit_stalk_kernel`
(node `lem-weil-pbc-closed-immersion-unit-stalk-kernel`). Its proof is exactly
`by sorry`, with source and a complete natural-language argument in its docstring.
The first worker's `closedImmersion_unit_kernel_fork` hole and module are removed.
No definitions or arbitrary witness constructions were added.

Against the original item: one hole closed, one hole added, net zero.
This delivery is a decomposition with a fully proved epi component, not a
claim that the whole item is proved without sorry. Compared with the submitted
first-worker sandbox, the number of remaining holes falls from two to one.
The pinned sorry ledger, rather than these local counts, determines closure progress.

Local compilation of all three delivered modules passes without errors or warnings.
Scratch `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`
for the epi helper; the remaining local theorem and the target additionally use
`sorryAx`, as reported above. No forbidden declarations or proof mechanisms occur.

## No longer needed

Removed these plain imports from the target:
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`;
- `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`;
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.

The first three are still reached through the proved epi helper, and tensor
products remain supplied by the existing public interfaces. No entire existing
module is claimed pruned from the targets' closure.

Every original direct proof dependency omitted by the new target proof_deps:
- `lem-weil-pbc-module-iso-on-stalks`: the proof uses exactness detection and
  `Exact.fIsKernel`, so no isomorphism-on-stalks comparison is needed;
- `lem-weil-pbc-locally-surjective-iff-stalks`: the epi helper directly proves
  cancellation from stalk surjectivity and section_ext;
- `lem-weil-pbc-closed-pushforward-stalks`: now a dependency of the epi helper
  and the local kernel calculation, rather than a direct target step;
- `def-weil-closed-immersion`: retained in the target statement dependencies
  and helper proofs, but no direct target proof step unfolds this definition;
- `lem-weil-pbc-module-stalk-pullback`: now used by the epi helper and local
  kernel calculation rather than the target's global argument.

The unsubmitted first-worker kernel-fork module and node are no longer needed.
The new reduction also avoids `Sheaf.AlgebraicGeometry.StalkImageRange` and its
open image-range theorem; these were not imports of the original item.

## Where the brief, the DAG or earlier work was wrong

The first worker merely applied two new sorry theorems stating the two conjuncts.
That gave no real reduction, kept all direct proof imports unused, omitted the
updated target DAG node, and left insufficient proof docstrings on the new holes.
The new epi proof and global kernel reduction repair those problems.
The copied helper nodes also carried unrelated maintainer review records and
empty statement/proof dependencies; rebuilt these new nodes with the actual
interfaces and arguments, without claiming a maintainer review.

Read the source at [Stacks 08KS](https://stacks.math.columbia.edu/tag/08KS) and
[Stacks 04CJ](https://stacks.math.columbia.edu/tag/04CJ), since this machine lacks
the literature checkout. 04CJ works on the small etale site; the Zariski stalk
argument needed here is the ringed-space argument of 08KS, with the local
quotient-kernel calculation written out. No quasi-coherence or finite generation
is assumed or used in the delivered declarations.

## New nodes

`lem-weil-pbc-closed-immersion-unit-epi` records the now complete epi proof.
It is a genuinely proved helper, not a new deferred conjunct.

`lem-weil-pbc-closed-immersion-unit-stalk-kernel` records only the missing local
linear-algebra identification at one point. Its docstring treats both the
closed image and its complement, explains the ideal-stalk identification,
the pure-tensor map, the quotient inverse, and the chosen-adjunction transport.
The existing tensor multiplication range and stalk comparison lemmas do not
already identify this kernel. No change record is required.

Searches used new wording: LeanFinder for quotient extension-unit surjectivity
and for the stalk kernel, Loogle for `IsClosedImmersion`/`stalkMap` and
`LinearMap.range, LinearMap.ker, TensorProduct`, and rg over Mathlib and both
library roots. Read `TensorProduct.mk_surjective`,
`TensorProduct.quotTensorEquivQuotSMul`, `Ideal.subtype_rTensor_range`, and the
existing geometric comparison statements. LeanSearch was attempted for both
new nodes but returned Internal Server Error; the nodes record unavailability
without inventing a no-match verdict. Blueprint search found no duplicate.

## Second reading by N3

1. Compared the target module with the repository by diff and the declaration
   parser. Existing signatures and the original docstring are byte for byte
   identical; there are no changed definitions or unreported adaptations.
   Verdict: pass.
2. Compiled every delivered file with lcompile.py, then compiled a scratch
   target copy with #print axioms for all three declarations. Epi has only
   the three permitted axioms; the target and local kernel theorem additionally
   have the explicitly reported sorryAx. Exactly one named theorem has sorry,
   and no axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   occurs. Verdict: pass as a decomposition, not a sorry-free target proof.
3. Read the local kernel statement and docstring against 08KS and the existing
   stalk interfaces. Tested mathematically: F=0; i the identity (J=0 and unit
   invertible); Z empty (J is the unit ideal and target zero); affine quotient
   Z -> Z/2 with M=Z (kernel 2Z), and M=Z/2 (kernel zero, no flatness required).
   The arbitrary adjunction only postcomposes the canonical unit with an
   isomorphism. The new local statement is true under exactly the supplied
   hypotheses. Searches found component comparisons, not a duplicate.
   Verdict: pass. Rejected the first worker's conjunct-restatement split.
4. Replaced that split with a formal epi proof and a global reduction from one
   stalk calculation. Read dag/units/sk-thm-p1.json realized statement and
   steps; none is removed or bypassed. The change is below the unit level.
   Removed all unused plain target imports and listed every omitted original
   direct proof dependency above; no whole-module pruning is claimed.
   Verdict: pass.
5. Read all delivered nodes against the final Lean. The target route uses the
   epi helper, the local multiplication range equality, module_stalk_exact,
   the canonical image isomorphism and Mathlib exact-to-kernel machinery.
   Each proof_deps list equals the union of proof-step uses. Both new nodes
   contain source, searches, Lean signature verbatim, creation, blueprint,
   chapter and unit records; the target node's statement is unchanged.
   Verdict: pass.

Changes in this second reading: proved the epi helper, removed the kernel-fork
restatement, added the genuine local kernel calculation and global proof,
pruned unused direct imports, rebuilt helper nodes and updated the target
proof route, and rewrote the report to distinguish decomposition from completion.
