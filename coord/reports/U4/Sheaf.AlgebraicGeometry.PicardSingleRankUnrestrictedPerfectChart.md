## What changed

Proved the body of `AlgebraicGeometry.Scheme.exists_picardSingleRankUnrestrictedPerfectChart`
without changing its signature, visibility, or existing docstring. Added the ordinary-sheaf
normal-form theorem in `Sheaf.AlgebraicGeometry.PicardRankMatchDirectImage`. The fixed-rank
case uses the existing proper flat affine Cech perfect model, K-flatness, and explicit
base-change comparisons. The mixed-fibre case uses the actual zero object and zero complex,
with proved perfectness, tensor vanishing, and the rank-one/empty-scheme equivalence.
All added imports are proof-only. Updated the chart node to the implemented proof route.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_picardSingleRankUnrestrictedPerfectChart`
(node `lem-sc-picard-single-rank-unrestricted-perfect-chart`). Its module has no remaining
sorry. The private zero/perfect/tensor/rank helpers are all proved.

Added: `AlgebraicGeometry.Scheme.exists_picardRankMatchDirectImageNormalForm`
(node `lem-sc-picard-rank-match-direct-image-normal-form`), whose whole proof is `by sorry`.
This has no derived category, complex, perfectness, or tensor-amplitude conclusion and is
strictly the ordinary geometric rank-comparison part of the argument. One hole closed and
one added: a decomposition, not a net proof. Existing imported holes remain in their own
modules; this delivery changes none of them.

## No longer needed

No original import was removed; every original public import supports the existing
signature. No globally unreachable module is claimed pruned. The chart no longer directly
uses `lem-pc-rf-perfect-base-change` or `lem-weil-pbc-flat-lfp-open`: it uses the affine Cech
perfect-model theorem for the derived construction and the new ordinary normal-form node
for fibre geometry. The openness and perfection arguments remain below those dependencies.
The fixed-rank source chart is not imported: its affine Cech conversion argument is written
inside this proof using already published dependencies. No unit statement or realized step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The proof dependency list lacked an ordinary rank-comparison interface for the unrestricted
homogeneous/empty/mixed cases. The existing structure-unit chart requires connected and
nonempty fibres and cannot be applied here. The new ordinary normal-form theorem fills
only that gap, with the complete three-case proof in its docstring and node. Its edge cases
include rank zero, empty tests, empty sources, nonreduced tests, and arbitrary base changes.
The new statement agrees with the unrestricted adaptation already in the parent node;
Stacks 0BDP itself additionally assumes the structure-sheaf unit and is not claimed to
state the unrestricted result verbatim.

The source of `ProperFlatDirectImagePerfectChart` was present but its compiled artifact was
absent from the published local build. Instead of copying or changing that module, this
proof uses its available affine Cech-model dependencies and the same explicit conversion
argument. Single-file local compilation passed without warnings.

## New nodes

`lem-sc-picard-rank-match-direct-image-normal-form` states only the ordinary reference-rank
normal form and is in the parent's chapter and unit. Its three proof steps are the
homogeneous, empty-fibre, and mixed-fibre cases. Searches found affine module rank-locus
lemmas but no exact ordinary universal predicate normal form; LeanSearch returned an
internal-server error and is recorded unavailable. Blueprint searches for rank and Picard
found no existing blueprint node stating this unrestricted ordinary comparison.
No definition, existing statement, or interface was changed, so no change record is needed.

## Second reading by U4

1. **Statements and accidental changes.** Compared both delivered modules with the repository versions. The existing target theorem signature and docstring are byte-for-byte unchanged; the new normal-form theorem is a separate declaration. No existing definition or public interface was changed. Verdict: pass.

2. **Proof validity.** Compiled `PicardRankMatchDirectImage.lean` successfully with `lcompile.py`. The target proof contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declaration; its only remaining hole is the named normal-form theorem in the added module. The target proof uses actual zero objects and explicit affine Cech data rather than an arbitrary witness. Verdict: pass, with the normal-form theorem intentionally split off.

3. **Split-off statement.** The normal-form statement is strictly the ordinary rank-comparison portion: it has no derived-category, perfectness, tensor, or amplitude conclusion. Its node has source, proof steps, dependencies, searches, and a complete docstring proof covering homogeneous, empty, and mixed-rank cases. It is not duplicated by a declaration found in the library or Mathlib. Verdict: pass.

4. **Pruning and route.** Proof-only imports support the explicit affine Cech/K-flat construction and zero-complex branch. The unit route remains represented by the chart node and its realized dependencies; no original public import was removed and no unreachable module is claimed pruned. Verdict: pass.

5. **DAG agreement.** The chart node proof and `proof_deps` now follow the actual normal-form, affine Cech comparison, and zero-complex proof. The added node records the exact Lean declaration and matching statement. Verdict: pass.

Changed after review: appended this second-reading record only; no Lean proof or statement changes were needed.
