## What changed

Proved `AlgebraicGeometry.affine_completion_baseChange_unit` with its signature and public
imports unchanged. The algebraic argument constructs the quotient equivalence directly
from completion evaluation and Mathlib's tensor quotient equivalences, including the
formula on the tensor unit. It does not assume that T is finite.

Added `Sheaf.AlgebraicGeometry.AffineFormalQuotientComparison`, whose public theorem
`AlgebraicGeometry.affine_formalQuotient_comparison` is proved from the existing affine
projection and ideal-power pullback image theorems. It identifies each explicit sheaf
quotient with the sheafification of the module quotient and verifies the projection
identity. The Spec argument uses the tilde adjunction triangle; the affine transport uses
uniqueness of left adjoints and the cokernel/image comparison. All new helpers are proved.

The original theorem combines these comparisons by cancelling the cokernel projection,
then uses the componentwise criterion for a natural transformation to be invertible.
Both delivered modules compile cleanly through lcompile.py, in about 20 and 14 seconds.
No existing declaration signature, visibility, definition, or target changed.

## Proved and sorry left

Closed the original one hole: `AlgebraicGeometry.affine_completion_baseChange_unit`
(node `lem-weil-pbc-affine-completion-baseChange-unit`).

Added zero holes. `AlgebraicGeometry.affine_formalQuotient_comparison` and all private
helpers are proved. There are no `sorry`s in either delivered module. The proof still
uses existing declarations whose upstream proofs may contain holes, particularly
`AlgebraicGeometry.formalModuleQuotient_affine_projection`; this delivery does not
claim to have closed those upstream holes.

## No longer needed

Removed no original import: all three public imports support the unchanged signature.
No source module can be claimed globally unreachable from this local delivery.

The old plan's `lem-weil-pbc-adic-completion-mod-ideal` is replaced by the positive-power
Mathlib leaf `lem-weil-pbc-adic-completion-mod-power` (05GG). The standalone
`lem-weil-pbc-tensor-right-exact` is not needed: Mathlib's explicit
`TensorProduct.quotientTensorEquiv` and `TensorProduct.quotTensorEquivQuotSMul` supply
quotient equivalences directly, with the tensor image calculation proved locally.
No import of `Mathlib.LinearAlgebra.TensorProduct.RightExactness` is added.
Second reading removed two redundant imports from the new comparison module:
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` (the latter is publicly
imported by the needed cokernel module). No original module was pruned.
The affine projection, tilde, and ideal-power pullback image dependencies remain needed,
through the proved affine quotient comparison.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and unit route were correct. The proof plan named the
first-power completion quotient, whereas the actual proof needs arbitrary powers; the
DAG now names the existing Mathlib leaf for those powers. The raw pullback image theorem
uses tensorPullback, while the target uses Mathlib pullback. The proof supplies the
natural isomorphism by uniqueness of left adjoints and transports quotient projections.

The planned exactness statements did not directly supply the projection-compatible
isomorphism on a general affine X. That compatibility is now proved explicitly,
without a new hole. Edge cases were checked mathematically: zero ideal gives ordinary
quotients, unit ideal gives zero quotients, zero modules give zero objects, and the empty
affine scheme gives the zero ring. All constructions use these same formulas.

The cited sources were read online at Stacks Tags 05GG, 01I8 and 0889; the local literature
checkout on this machine has citation tables but no Stacks tex files. No source file was
changed. No arbitrary data is selected from a mere unproved existence theorem; the only
selected adjunction determines the comparison by uniqueness of adjoints.

## New nodes

`lem-weil-pbc-affine-formal-quotient-comparison` records the proved, general positive
quotient comparison, in `Sheaf.AlgebraicGeometry.AffineFormalQuotientComparison`. It is
strictly the geometric step of the original argument: it mentions neither completion
nor the tensor unit, and applies to any affine scheme and module without Noetherianity.
Its proof uses the existing affine projection theorem, quasi-coherence closure, and the
ideal-power pullback image theorem. There are no change records or forced adaptations.

## Second reading by D3

1. **Unchanged interface: PASS.** Read the full diff against the repository. The existing
   theorem's signature is byte-for-byte unchanged; its docstring, visibility and three
   public imports are unchanged. All added proof imports are plain imports. There are
   no changed existing definitions, new instances, change records or forced adaptations.
2. **Proof and compilation: PASS.** Compiled both modules in dependency order using
   lcompile.py, without errors or warnings. Scanned for sorry and forbidden declarations:
   none occur in either delivered module. Scratch copies with #print axioms show only
   propext, Classical.choice and Quot.sound for the two algebraic private helpers; the
   public comparison and item additionally use sorryAx from existing upstream holes,
   including formalModuleQuotient_affine_projection. The private quotientFunctor has
   explicit object and morphism constructions and proved functor laws. The selected
   tensor-pullback adjunction supplies a comparison by uniqueness of left adjoints;
   no arbitrary object is chosen from an unproved existence theorem.
3. **New statements and reuse: PASS.** There are no split-off unproved statements.
   The proved affine_formalQuotient_comparison is strictly the geometric quotient step,
   independent of completion and the tensor unit. Read all its helpers and projection
   identities. Checked zero and unit ideals, zero modules, the empty affine scheme,
   positive exponent one, and arbitrary non-finite modules; no extra assumption is
   needed. Repeated leanfinder, loogle and grep searches with cokernel/multiplication
   wording, and searched both library roots. No public theorem already provides this
   comparison. Existing similarly named quotient-section helpers are private or give
   different conclusions. Rechecked Stacks 05GG, 01I8, 087W and 0889 against the argument.
4. **Route and pruning: PASS, with import cleanup.** The proof first uses Mathlib's
   completion evaluation and tensor quotient equivalences, then existing sheaf projection
   and pullback-image results. Its cancellation argument identifies the actual induced
   map, not merely isomorphic source and target objects. No shorter existing theorem was
   found. Checked dag/units/sk-thm-p1.json realized: none of its statement or step nodes
   is bypassed. Every old dependency is accounted for: mod-ideal and tensor-right-exact
   are replaced; projection, pullback-image and tilde remain used through the comparison.
   Removed redundant Kernels and QuasicoherentKernel imports from the new module;
   no original import or globally unreachable module is claimed pruned.
5. **DAG agreement: PASS after repair.** Compared the existing node diff: only proof,
   proof_deps and proof_origin change. Read the new node's source, statement, searches,
   blueprint, creation fields and verbatim Lean statement. Its first proof step uses
   ideal_times_quasiCoherent_affine_sections for quasi-coherence of positive ideal powers;
   added the missing lem-weil-pbc-ideal-times-quasi-coherent-affine-sections to that step's
   uses and the union proof_deps. All other steps describe the actual proof.

Second reading changed only the two redundant imports, the missing new-node proof
 dependency, and this report. One original hole closed, zero holes added; this is a proof
 relative to existing dependencies, not a decomposition. No Lean proof body changed.
